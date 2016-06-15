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
{{range $key, $value := .Funcs}}
	<p><a href={{$key}}>{{$key}}</a> <b>{{$value}}</b></p>
	{{end}}
</body>
</html>
`

type CFunc struct {
	name     string
	params   string
	body     string
	filename string
	calling  []*CFunc
}

type Func struct {
	Name     string
	Filename string
}
type CFuncs struct {
	Funcs map[string]string
}

type CMACRO struct {
	name     string
	value    string
	filename string
}

var macroDB = make(map[string]*CMACRO, 1000)

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
	level                  int
}

type Graph struct {
	gw, gh         int /* graph size */
	ew, eh         int /* element size */
	sw, sh         int /* Start point */
	deltaw, deltah int /* delta value between to elements */
	pix            int /* pixls */
	rows           map[int]*RowGraph
	graphs         map[string]*CFuncGraph
}

type RowGraph struct {
	x, y    int
	element []*CFuncGraph
}

var constGraph = Graph{gw: 4000, gh: 4000, ew: 0, eh: 15, sw: 1000, sh: 40, deltaw: 20, deltah: 40, pix: 5}

type CallTreeSPF struct {
	root   string
	vertex map[string]*SPFVertex
	rows   map[int][]*SPFVertex
	level  int
}

type SPFVertex struct {
	fn       *CFunc
	level    int
	drawed   bool
	children []*SPFVertex
}

var filterFuncList = `sizeof, memset, memcpy, htons, ntohs, hton, ntoh, likely, in_irq, if, switch, for, while, dev_net`

var CFuncList = make(map[string]*CFunc, 10000)

var FetchFunctionDefinition = regexp.MustCompile(`(?P<funcName>[[:word:]_]+)[[:space:]]*(?P<funcParams>\([[:word:][:space:]\-\>\,\_\*]*\))[[:space:]]+\{`)
var FetchMACRODefinition = regexp.MustCompile(`[[:space:]]*#define[[:space:]]+(?P<MACROName>[[:word:]_]+)[[:space:]]+`)

var FetchFunctionCall = regexp.MustCompile(`(?P<funcName>[[:word:]_]+)[[:space:]]*(?P<funcParams>\([[:word:][:space:]\-\>\,\_\*\&\-\>\"\'\(\)]*\))[[:space:]]*[\;\)\+\-\*\/\&\|\,\?]+`)

//var FetchFunctionCall = regexp.MustCompile(`(?P<funcName>[[:word:]_]+)[[:space:]]*(?P<funcParams>\([[:word:][:space:]\-\>\,\_\*\&\-\>]*\))[[:space:]]*\;+`)

func (spf *CallTreeSPF) getSubVertex(v *CFunc) {
	if v == nil || len(v.calling) == 0 {
		return
	}

	spf.vertex[v.name].children = make([]*SPFVertex, 0, len(v.calling))
	for _, fi := range v.calling {
		if _, ok := spf.vertex[fi.name]; ok {
			continue
		}

		if fi != nil {
			nv := new(SPFVertex)
			nv.fn = fi
			nv.level = spf.vertex[v.name].level + 1
			if spf.level < nv.level {
				spf.level = nv.level
			}
			nv.drawed = false
			spf.vertex[fi.name] = nv
			spf.vertex[v.name].children = append(spf.vertex[v.name].children, nv)
			spf.getSubVertex(fi)
		}
	}
}

func (spf *CallTreeSPF) getVertex() error {
	if r, ok := CFuncList[spf.root]; ok {
		spf.vertex = make(map[string]*SPFVertex, 200)
		nv := new(SPFVertex)
		nv.fn = r
		nv.level = 0
		nv.drawed = false
		if spf.level < nv.level {
			spf.level = nv.level
		}
		spf.vertex[spf.root] = nv
		if len(r.calling) != 0 {
			spf.getSubVertex(r)
		}
	}

	spf.rows = make(map[int][]*SPFVertex, spf.level)
	spf.rows[0] = append(spf.rows[0], spf.vertex[spf.root])
	spf.vertex[spf.root].drawed = true
	for l := 1; l <= spf.level; l++ {
		for _, p := range spf.rows[l-1] {
			for _, c := range p.children {
				if spf.vertex[c.fn.name].drawed == true {
					continue
				}
				spf.rows[l] = append(spf.rows[l], c)
				spf.vertex[c.fn.name].drawed = true
			}
		}
	}
	/*
		for _, v := range spf.vertex {
			spf.rows[v.level] = append(spf.rows[v.level], v)
		}
	*/
	return nil
}

func addNewFunc(filename string, buf []byte, funFigure string, funName string, funParams string) error {
	if _, ok := CFuncList[funName]; ok {
		return errors.New("Already exist: " + funName)
	}
	fun := new(CFunc)
	fun.name = funName
	fun.params = funParams
	fun.filename = filename
	fun.body = getFuncBody(string(buf), funFigure[:len(funFigure)-2]) /* For " {" */
	CFuncList[funName] = fun

	return nil
}

func buildRowGraph(level int, row []*SPFVertex) *RowGraph {
	rg := new(RowGraph)
	rlen := 0
	for _, v := range row {
		rlen = rlen + len(v.fn.name)*constGraph.pix + constGraph.deltaw
	}

	rg.x = constGraph.sw - rlen/2
	rg.y = constGraph.sh + (constGraph.eh+constGraph.deltah)*level
	rg.element = make([]*CFuncGraph, 0, len(row))
	sw := rg.x
	sh := rg.y
	for _, v := range row {
		var graph = new(CFuncGraph)
		graph.name = v.fn.name
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
		graph.level = level
		rg.element = append(rg.element, graph)
		constGraph.graphs[graph.name] = graph
		sw += graph.w + constGraph.deltaw
	}

	return rg
}

func buildFuncCallTreeGraph(spf *CallTreeSPF) {
	constGraph.rows = make(map[int]*RowGraph, spf.level)
	constGraph.graphs = make(map[string]*CFuncGraph, len(spf.vertex))
	for i, row := range spf.rows {
		constGraph.rows[i] = buildRowGraph(i, row)
	}

}

func drawFuncCallTree(w http.ResponseWriter, spf *CallTreeSPF) {
	if spf == nil {
		return
	}
	w.Header().Set("Content-Type", "image/svg+xml")
	s := svg.New(w)
	s.Start(constGraph.gw, constGraph.gh)
	for _, row := range constGraph.rows {
		for _, g := range row.element {
			s.Roundrect(g.x, g.y, g.w, g.h, 1, 1, "fill:none;stroke:black")
			s.Link(g.name, g.name)
			s.Text(g.tx, g.ty, g.name, "text-anchor:middle;font-size:5px;fill:black")
			s.LinkEnd()
		}
	}

	for _, v := range spf.vertex {
		for _, subv := range v.children {
			s.Line(constGraph.graphs[v.fn.name].dmpx, constGraph.graphs[v.fn.name].dmpy, constGraph.graphs[subv.fn.name].umpx, constGraph.graphs[subv.fn.name].umpy, "fill:none;stroke:black")
		}
	}
	s.End()
}

func createFuncGraph(w http.ResponseWriter, r *http.Request) {
	fmt.Println(r.URL.Path[1:])
	if fn, ok := CFuncList[r.URL.Path[1:]]; ok {
		spf := new(CallTreeSPF)
		spf.root = fn.name
		spf.level = 0
		spf.getVertex()
		buildFuncCallTreeGraph(spf)
		drawFuncCallTree(w, spf)
	} else {
		io.WriteString(w, "No exit in global list\n")
	}
}

func buildCallTree() {
	for _, fi := range CFuncList {
		if FetchFunctionCall.MatchString(fi.body) {
			callList := FetchFunctionCall.FindAllStringSubmatch(fi.body, -1)
			var callbackCount = 0
			for _, cf := range callList {
				params := strings.Split(cf[2][1:len(cf[2])-1], ",")
				for _, p := range params {
					p = strings.Replace(p, " ", "", -1)
					if _, ok := CFuncList[p]; ok {
						callbackCount++
					}
				}
			}
			fi.calling = make([]*CFunc, 0, len(callList)+callbackCount)
			for _, cf := range callList {
				if e, ok := CFuncList[cf[1]]; ok {
					fi.calling = append(fi.calling, e)
					params := strings.Split(cf[2][1:len(cf[2])-1], ",")
					for _, p := range params {
						p = strings.Replace(p, " ", "", -1)
						if cb, ok := CFuncList[p]; ok {
							fi.calling = append(fi.calling, cb)
						}
					}
				} else {
					if strings.Contains(filterFuncList, cf[1]) {
						continue
					}

					if _, ok := macroDB[cf[1]]; ok {
						continue
					}
					nf := new(CFunc)
					nf.name = cf[1]
					nf.params = cf[2]
					fi.calling = append(fi.calling, nf)
					params := strings.Split(cf[2][1:len(cf[2])-1], ",")
					for _, p := range params {
						p := strings.Replace(p, " ", "", -1)
						if cb, ok := CFuncList[p]; ok {
							fi.calling = append(fi.calling, cb)
						}
					}
				}
			}
		}
		/*
			for k, f := range CFuncList {
				funcCallRe := regexp.MustCompile(k + `[[:space:]]*\([[:word:][:space:]\,\-\>\*\&\!\+\=]*\)`)
				if funcCallRe.MatchString(fi.body) {
					fi.calling[k] = f
					f.called[fn] = fi
				}
			}
		*/
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
		s.Roundrect(sw, sh, len(v)*5, h, 1, 1, "fill:none;stroke:black")
		s.Text((sw+len(v)*5)-(len(v)*5)/2, sh+10, v, "text-anchor:middle;font-size:5px;fill:black")

		sw += len(v)*5 + 20
	}
	s.End()
}

func showFuncList(w http.ResponseWriter, req *http.Request) {
	req.ParseForm()
	fmt.Println("Path: ", req.URL.Path)
	var funcList = CFuncs{Funcs: make(map[string]string, len(CFuncList))}

	if req.URL.Path == "/" {
		for fn, fi := range CFuncList {
			if len(fi.calling) == 0 {
				continue
			}
			funcList.Funcs[fn] = fi.filename
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
}

func getFuncBody(buf string, figure string) string {
	index := strings.Index(buf, figure)
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
	body = body[bstart : bstart+bsize-1]
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

	fstr := strings.TrimSpace(strings.Replace(strings.Replace(strings.Trim(strings.Trim(strings.Trim(string(buf), "\n"), "\t"), " "), "\n", " ", -1), "\t", " ", -1))
	if FetchMACRODefinition.MatchString(fstr) {
		macroList := FetchMACRODefinition.FindAllStringSubmatch(fstr, -1)
		for _, m := range macroList {
			macro := new(CMACRO)
			macro.name = m[1]
			macro.filename = filename
			macroDB[m[1]] = macro
		}
	}
	if FetchFunctionDefinition.MatchString(fstr) {
		funcList := FetchFunctionDefinition.FindAllStringSubmatch(fstr, -1)
		for _, v := range funcList {
			if v[1] != "if" && v[1] != "switch" && v[1] != "for" && v[1] != "while" {
				if !strings.Contains(v[2], "void") {
					if strings.Contains(v[2], ",") {
						if params := strings.Split(v[2], ","); params != nil {
							if !strings.Contains(params[0], " ") {
								continue
							}
						}
						addNewFunc(filename, []byte(fstr), v[0], v[1], v[2])

					} else {
						if !strings.Contains(v[2], " ") {
							continue
						} else {
							addNewFunc(filename, []byte(fstr), v[0], v[1], v[2])
						}

					}
				} else {
					addNewFunc(filename, []byte(fstr), v[0], v[1], v[2])
				}
			}
		}
	}

	/*
		if FetchFunctionCall.MatchString(fstr) {
			funcList := FetchFunctionCall.FindAllStringSubmatch(fstr, -1)
			for _, v := range funcList {
				fmt.Println(v[1])
			}
		}
	*/

	return nil
}

func fileParse(filename string, fi os.FileInfo, err error) error {
	if fi.IsDir() {
		fmt.Println("DIR " + filename)
	} else {
		if strings.HasSuffix(filename, ".c") || strings.HasSuffix(filename, ".h") {
			getFuncList(filename)
		}
	}
	return nil
}

func main() {
	if len(os.Args) < 2 {
		usuage()
		os.Exit(1)
	}

	list := strings.Split(os.Args[1], " ")
	for _, arg := range list {
		fInfo, err := os.Lstat(arg)
		if err != nil {
			usuage()
			fmt.Println(err.Error())
			os.Exit(2)
		}

		if fInfo.IsDir() {
			err = filepath.Walk(arg, fileParse)
		} else {
			fmt.Println("File " + arg)
			getFuncList(arg)
		}
	}

	buildCallTree()
	http.Handle("/", http.HandlerFunc(showFuncList))
	http.Handle("/circle", http.HandlerFunc(dumpFuncList))
	err := http.ListenAndServe(":2003", nil)
	if err != nil {
		fmt.Println(err.Error())
	}
}
