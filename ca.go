package main

import (
	"errors"
	"fmt"
	"github.com/ajstarks/svgo"
	"html/template"
	"io"
	"io/ioutil"
	"net/http"
	"os"
	"path/filepath"
	"regexp"
	"runtime/pprof"
	"strings"
)

func usuage() {
	fmt.Println("Usuage:")
	fmt.Println("\t\t ca XXX")
}

const (
	funclist = "function_list.txt"
)

var tmpl = `<!DOCTYPE html>
<html lang="en">
<head>
	<meta charset="UTF-8">
	<title>Func list</title>
</head>

<body>
	{{range .Funcs}}
	<p><a href={{.}}>{{.}}</a></p>
	{{end}}
</body>
</html>
`

type CFunc struct {
	name    string
	params  string
	body    string
	calling map[string]*CFunc
	called  map[string]*CFunc
}

type CFuncs struct {
	Name  string
	Funcs []string
}

/*
    x,y        w ump
	----------------------
        |                    |
       h|                    |
        |                    |
	----------------------
	         dmp
*/
type CFuncGraph struct {
	x, y                   int
	tx, ty                 int
	w, h                   int /* width, height */
	umpx, umpy, dmpx, dmpy int /* up middler port, down middler point */
	name                   string
	chsw, chsh             int /* children grap start point */
	children               map[string]*CFuncGraph
	level                  int
}

type Graph struct {
	gw, gh         int /* graph size */
	ew, eh         int /* element size */
	sw, sh         int /* Start point */
	deltaw, deltah int /* delta value between to elements */
	pix            int /* pixls */
}

var constGraph = Graph{gw: 2000, gh: 2000, ew: 0, eh: 15, sw: 1000, sh: 40, deltaw: 20, deltah: 40, pix: 5}

var level = 0

var CFuncList = make(map[string]*CFunc, 10000)

var FetchFunction = regexp.MustCompile(`(?P<funcName>[[:word:]_]+)[[:space:]]*(?P<funcParams>\([[:word:][:space:]\-\>\,\_\*]*\))[[:space:]]+\{`)

//var FetchFunction = regexp.MustCompile(`(?P<funcName>[[:word:]_]+)[[:space:]]*(?P<funcParams>\([[:word:][:space:]\*\,]*\))[[:space:]]+\{`)

func addNewFunc(buf []byte, funFigure string, funName string, funParams string) error {
	if _, ok := CFuncList[funName]; ok {
		return errors.New("Already exist: " + funName)
	}
	fun := new(CFunc)
	fun.name = funName
	fun.params = funParams
	fun.body = string(getFuncBody(buf, funName+funParams))
	fun.calling = make(map[string]*CFunc, 50)
	fun.called = make(map[string]*CFunc, 50)
	CFuncList[funName] = fun

	/*
		fmt.Println(funName + funParams)
		fmt.Println(fun.body)
	*/

	return nil
}

func createChildrenGraph(root *CFuncGraph, fn *CFunc) {
	if fn == nil || len(fn.calling) == 0 {
		return
	}

	root.children = make(map[string]*CFuncGraph, len(fn.calling))
	sw := root.chsw
	sh := root.chsh
	for k, f := range fn.calling {
		var graph = new(CFuncGraph)
		graph.name = k
		graph.x = sw
		graph.y = sh
		graph.w = len(graph.name) * constGraph.pix
		graph.h = constGraph.eh
		graph.tx = graph.x + len(graph.name)*constGraph.pix - (len(graph.name)*constGraph.pix)/2
		graph.ty = graph.y + constGraph.eh - constGraph.pix
		graph.umpx = graph.x + graph.w/2
		graph.umpy = graph.y
		graph.dmpx = graph.x + graph.w/2
		graph.dmpy = graph.y + constGraph.eh
		graph.level = 0
		root.children[k] = graph
		sw += graph.w + constGraph.deltaw

		chlen := 0
		for i, _ := range f.calling {
			chlen = chlen + len(i)*constGraph.pix + constGraph.deltaw
		}
		graph.chsw = graph.umpx - chlen/2
		graph.chsh = graph.dmpy + constGraph.deltah + constGraph.eh

	}
}

func drawGraph(w http.ResponseWriter, root *CFuncGraph) {
	w.Header().Set("Content-Type", "image/svg+xml")
	s := svg.New(w)
	s.Start(constGraph.gw, constGraph.gh)
	s.Roundrect(root.x, root.y, root.w, root.h, 1, 1, "fill:none;stroke:black")
	s.Link(root.name, root.name)
	s.Text(root.tx, root.ty, root.name, "text-anchor:middle;font-size:5px;fill:black")
	s.LinkEnd()

	if len(root.children) != 0 {
		for _, g := range root.children {
			s.Roundrect(g.x, g.y, g.w, g.h, 1, 1, "fill:none;stroke:black")
			s.Link(g.name, g.name)
			s.Text(g.tx, g.ty, g.name, "text-anchor:middle;font-size:5px;fill:black")
			s.LinkEnd()
			s.Line(root.dmpx, root.dmpy, g.umpx, g.umpy, "fill:none;stroke:black")
		}
	}
	s.End()

}

func createFuncGraph(w http.ResponseWriter, r *http.Request) {
	if fn, ok := CFuncList[r.URL.Path[1:]]; ok {
		var root = CFuncGraph{name: fn.name, x: constGraph.sw, y: constGraph.sh}
		root.w = len(root.name) * constGraph.pix
		root.h = constGraph.eh
		root.tx = root.x + len(root.name)*constGraph.pix - (len(root.name)*constGraph.pix)/2
		root.ty = root.y + constGraph.eh - constGraph.pix
		root.umpx = root.x + root.w/2
		root.umpy = root.y
		root.dmpx = root.x + root.w/2
		root.dmpy = root.y + constGraph.eh
		root.level = 0

		chlen := 0
		for k, _ := range fn.calling {
			chlen = chlen + len(k)*constGraph.pix + constGraph.deltaw
		}
		root.chsw = root.umpx - chlen/2
		root.chsh = root.dmpy + constGraph.deltah + constGraph.eh

		if len(fn.calling) != 0 {
			createChildrenGraph(&root, fn)
		}

		drawGraph(w, &root)
	} else {
		io.WriteString(w, "No exit in global list\n")
	}
}

func buildCallTree() {
	for fn, fi := range CFuncList {
		for k, f := range CFuncList {
			if strings.Contains(fi.body, k) {
				fi.calling[k] = f
				f.called[fn] = fi
			}
		}
	}
}

func dumpFuncCall(fn *CFunc) {
	if fn == nil {
		return
	}
	if len(fn.calling) == 0 {
		return
	}

	for _, f := range fn.calling {
		if f != nil {
			if f == fn {
				continue
			}

			if _, ok := f.calling[fn.name]; ok {
				continue
			}
			fmt.Printf("---------------->" + f.name)
			fmt.Printf("Calling ")
			dumpFuncCall(f)
		}
	}
	return
}

func dumpCallTree() {
	for n, f := range CFuncList {
		level = 0
		fmt.Println("")
		fmt.Printf("[ " + n + " ] ")
		fmt.Println("Calling :")
		for _, fn := range f.calling {
			if fn != nil {
				fmt.Printf("\t" + fn.name + "\n")
			}
		}
		//dumpFuncCall(f)
	}
}

func dumpFuncList(w http.ResponseWriter, req *http.Request) {
	w.Header().Set("Content-Type", "image/svg+xml")
	s := svg.New(w)
	h := 15
	sw := 500
	sh := 500
	s.Start(100000, 100000)
	for v, _ := range CFuncList {
		fmt.Println(v)
		s.Roundrect(sw, sh, len(v)*5, h, 1, 1, "fill:none;stroke:black")
		s.Text((sw+len(v)*5)-(len(v)*5)/2, sh+10, v, "text-anchor:middle;font-size:5px;fill:black")

		sw += len(v)*5 + 20
	}
	s.End()
}

func showFuncList(w http.ResponseWriter, req *http.Request) {
	req.ParseForm()
	fmt.Println("Method: ", req.Method)
	fmt.Println("Path: ", req.URL.Path)
	var funcList = CFuncs{Name: "", Funcs: make([]string, 0, len(CFuncList))}

	if req.URL.Path == "/" {
		for fn, fi := range CFuncList {
			if len(fi.calling) == 0 {
				continue
			}
			funcList.Funcs = append(funcList.Funcs, fn)
		}
		t, err := template.New("main").Parse(tmpl)
		if err != nil {
			fmt.Println(err.Error())
			return
		}
		t.Execute(w, funcList)

		return
	}

	createFuncGraph(w, req)
	/*
		fmt.Println("--------------")
		fmt.Println(req.URL.Path[1:])
		if fn, ok := CFuncList[req.URL.Path[1:]]; ok {
			fmt.Println("++++++++++++++++++++++++++")
			funcList.Name = fn.name
			for name, _ := range fn.calling {
				funcList.Funcs = append(funcList.Funcs, name)
			}

			fmt.Println(funcList.Funcs)
			if len(funcList.Funcs) != 0 {
				w.Header().Set("Content-Type", "image/svg+xml")
				s := svg.New(w)
				h := 15
				sw := 100
				sh := 100
				s.Start(1000, 500)
				for _, v := range funcList.Funcs {
					s.Roundrect(sw, sh, len(v)*5, h, 1, 1, "fill:none;stroke:black")
					s.Link(v, v)
					s.Text((sw+len(v)*5)-(len(v)*5)/2, sh+10, v, "text-anchor:middle;font-size:5px;fill:black")
					s.LinkEnd()

					sw += len(v)*5 + 20
				}
				s.End()
			} else {
				io.WriteString(w, "Nothing\n")
			}
		} else {
			io.WriteString(w, "No exit in global list\n")
		}
	*/
}

func getFuncBody(buf []byte, figure string) []byte {
	index := strings.Index(string(buf), figure)
	body := buf[index+len(figure):]

	var brace_count = 0
	var bsize = 0
	var bstart = 0

	for _, c := range body {
		bsize++
		if c == '{' {
			if brace_count == 0 {
				bstart = 1
			}
			brace_count++
		} else if c == '}' {
			brace_count--
			if brace_count == 0 {
				break
			}
		}
	}
	body = body[bstart : bstart+bsize]
	return body
}

func getFuncList(filename string) error {
	file, err := os.Open(filename)
	defer file.Close()
	if err != nil {
		fmt.Println(err.Error())
		os.Exit(-1)
	}

	buf, err := ioutil.ReadAll(file)
	if err != nil {
		fmt.Println(err.Error())
		os.Exit(-2)
	}

	//	fmt.Println(strings.TrimSpace(strings.Replace(strings.Replace(strings.Trim(strings.Trim(strings.Trim(string(buf), "\n"), "\t"), " "), "\n", " ", -1), "\t", " ", -1)))

	fstr := strings.TrimSpace(strings.Replace(strings.Replace(strings.Trim(strings.Trim(strings.Trim(string(buf), "\n"), "\t"), " "), "\n", " ", -1), "\t", " ", -1))
	if FetchFunction.MatchString(fstr) {
		funcList := FetchFunction.FindAllStringSubmatch(fstr, -1)
		for _, v := range funcList {
			if v[1] != "if" && v[1] != "switch" && v[1] != "for" && v[1] != "while" {
				//				fmt.Println(FetchFunction.SubexpNames()[1])
				//				fmt.Println(FetchFunction.SubexpNames()[2])
				//				fmt.Println(v[2])
				if !strings.Contains(v[2], "void") {
					if strings.Contains(v[2], ",") {
						if params := strings.Split(v[2], ","); params != nil {
							if !strings.Contains(params[0], " ") {
								continue
							}
						}
						//	fmt.Println(v[1])
						//	fmt.Println(v[2])
						addNewFunc([]byte(fstr), v[0], v[1], v[2])

					} else {
						if !strings.Contains(v[2], " ") {
							continue
						} else {
							//		fmt.Println(v[1])
							//		fmt.Println(v[2])
							addNewFunc([]byte(fstr), v[0], v[1], v[2])
						}

					}
				} else {
					//fmt.Println(v[1])
					//fmt.Println(v[2])
					addNewFunc([]byte(fstr), v[0], v[1], v[2])
				}
			}
		}
	}

	/*
		//	fmt.Println(string(buf))
		fmt.Println(strings.TrimSpace(string(buf)))
		if FetchFunction.Match(buf) {
			funcList := FetchFunction.FindAllSubmatch(buf, -1)
			for _, v := range funcList {
				fmt.Printf("%q\n", v[0])
			}
		}
	*/
	return nil

}

func fileParse(filename string, fi os.FileInfo, err error) error {
	if fi.IsDir() {
		fmt.Println("DIR " + filename)
	} else {
		if strings.HasSuffix(filename, ".c") {
			getFuncList(filename)
		}
	}
	return nil
}

func main() {
	f, _ := os.Create("pprofile_file")
	pprof.StartCPUProfile(f)
	//	defer pprof.StopCPUProfile()

	if len(os.Args) != 2 {
		usuage()
		os.Exit(1)
	}

	fInfo, err := os.Lstat(os.Args[1])
	if err != nil {
		usuage()
		fmt.Println(err.Error())
		os.Exit(2)
	}

	if fInfo.IsDir() {
		err = filepath.Walk(os.Args[1], fileParse)
	} else {
		fmt.Println("File " + os.Args[1])
		getFuncList(os.Args[1])
	}

	buildCallTree()
	dumpCallTree()
	http.Handle("/", http.HandlerFunc(showFuncList))
	http.Handle("/circle", http.HandlerFunc(dumpFuncList))
	err = http.ListenAndServe(":2003", nil)
	if err != nil {
		fmt.Println(err.Error())
	}
}
