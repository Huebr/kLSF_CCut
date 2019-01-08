#include <iostream>                  // for std::cout
#include <utility>                   // for std::pair
#include <algorithm>                 // for std::for_each
#include <boost/graph/graph_traits.hpp> // for creation of descriptors vertex and edges.
#include <boost/graph/adjacency_list.hpp> //for usage of adjacency list
#include <boost/graph/filtered_graph.hpp>
#include <boost/graph/connected_components.hpp>
#include <ilcplex/ilocplex.h>
#include <unordered_set>
#include <boost/dynamic_bitset.hpp>
ILOSTLBEGIN //initialization make vs work properly

using namespace boost;

//basic definitions
typedef typename adjacency_list<vecS, vecS, undirectedS, no_property, property<edge_color_t, int>> graph_t;
typedef dynamic_bitset<> db;

template <typename EdgeColorMap, typename ValidColorsMap>
struct valid_edge_color {
	valid_edge_color() { }
	valid_edge_color(EdgeColorMap color, ValidColorsMap v_colors) : m_color(color), v_map(v_colors) { }
	template <typename Edge>
	bool operator()(const Edge& e) const {
		return v_map.test(get(m_color, e));
	}
	EdgeColorMap m_color;
	ValidColorsMap v_map;
};



template<class Graph, class Mask>
void print_filtered_graph(Graph &g, Mask valid) { //pay atention to the position of the bits and the colors positions in array
	typedef typename property_map<Graph, edge_color_t>::type EdgeColorMap;
	typedef typename boost::dynamic_bitset<> db;
	typedef filtered_graph<Graph, valid_edge_color<EdgeColorMap, db> > fg;

	valid_edge_color<EdgeColorMap, Mask> filter(get(edge_color, g), valid);
	fg tg(g, filter);
	print_edges(edges(tg).first, edges(tg).second, tg);
}
template<class Graph, class Mask>
int get_components(Graph &g, Mask &m, vector<int> &components) {
	typedef typename property_map<Graph, edge_color_t>::type EdgeColorMap;
	typedef typename boost::dynamic_bitset<> db;
	typedef filtered_graph<Graph, valid_edge_color<EdgeColorMap, db> > fg;

	valid_edge_color<EdgeColorMap, Mask> filter(get(edge_color, g), m);
	fg tg(g, filter);
	int num = connected_components(tg, &components[0]);
	return num;
}

template<class Graph>
property_map<graph_t, edge_color_t>::type get_colors(Graph &g) {
	typedef typename property_map<Graph, edge_color_t>::type ColorMap;
	ColorMap colors = get(edge_color,g);
	//make color type generic
	return colors;
}


//Callbacks new to me new to you let god save my soul

ILOUSERCUTCALLBACK2(MyCuts, IloBoolVarArray, z, graph_t, g) {
	int size = z.getSize();
	db temp(size);
	std::vector<int> components(num_vertices(g));
	auto colors = get_colors(g);
	graph_traits<graph_t>::edge_iterator it, end;
	for (int i = 0; i < size; ++i) { //using colors of original graph
		if (getValue(z[i])>0.0) temp.set(i);
	}
	std::cout << " user cutting" << std::endl;
	int num_c = get_components(g, temp, components);
	if (num_c > 1) {
		std::cout << "add user cut" << std::endl;
		db temp1(size);
		std::tie(it, end) = edges(g);
		IloExpr expr(getEnv());
		while (it != end) {
			if (components[source(*it, g)] != components[target(*it, g)]) {
				if (components[source(*it, g)] == 0 || components[target(*it, g)] == 0) {
					temp1.set(colors[*it]);
				}
			}
			++it;
		}
		for (int i = 0; i < z.getSize(); ++i) if (temp1.test(i))expr += z[i];
		add(expr >= 1).end();
		expr.end();
	}
	else std::cout << "is good" << std::endl;
}



ILOLAZYCONSTRAINTCALLBACK2(LazyCallback, IloBoolVarArray,z,graph_t,g) {
	int size = z.getSize();
	db temp(size);
	std::vector<int> components(num_vertices(g));
	auto colors = get_colors(g);
	graph_traits<graph_t>::edge_iterator it, end;
	for (int i = 0; i < size  ; ++i) { //using colors of original graph
		if (getValue(z[i])>0.0) temp.set(i);
	}
	std::cout << "lazy cutting"<<std::endl;
	int num_c = get_components(g,temp,components);
	if (num_c > 1) {
		std::cout << "add cut" << std::endl;
		db temp1(size);
		std::tie(it,end) = edges(g);
		IloExpr expr(getEnv());
		while (it != end) {
			if (components[source(*it,g)]!=components[target(*it, g)]) {
				if (components[source(*it, g)] == 0 || components[target(*it, g)] == 0) {
					temp1.set(colors[*it]);
				}
			}
			++it;
		}
		for (int i = 0; i < z.getSize(); ++i) if(temp1.test(i))expr += z[i];
		add(expr >= 1).end();
		expr.end();
	}
	else std::cout << "found optimal" << std::endl;
}




//template function to print edges.
template<class EdgeIter, class Graph>
void print_edges(EdgeIter first, EdgeIter last, const Graph& G) {
	typedef typename property_map<Graph, edge_color_t>::const_type ColorMap;
	ColorMap colors = get(edge_color, G);
	//make color type generic
	//typedef typename property_traits<ColorMap>::value_type ColorType;
	//ColorType edge_color;
	for (auto it = first; it != last; ++it) {
		std::cout << "Edge: " << "(" << source(*it, G) << "," << target(*it, G) << ") " << " Color: " << colors[*it] << "\n";
		std::cout << "Edge: " << "(" << target(*it, G) << "," << source(*it, G) << ") " << " Color: " << colors[*it] << "\n";
	}
	std::cout << " Number of vertex: " << num_vertices(G) << std::endl;
	std::cout << " Number of edges: " << num_edges(G) << std::endl;
	std::vector<int> components(num_vertices(G));
	int num = connected_components(G, &components[0]);
	std::vector<int>::size_type i;
	std::cout << "Total number of components: " << num << std::endl;
	for (i = 0; i != components.size(); ++i)
		std::cout << "Vertex " << i << " is in component " << components[i] << std::endl;
	std::cout << std::endl;
}
template<class Graph>
void buildCCutModel(IloModel mod,IloBoolVarArray Z, const int k, const Graph &g) {
	IloEnv env = mod.getEnv();
	int n_colors = Z.getSize();
	int f_colors = n_colors - num_vertices(g) + 1;
	//setting names to labels variables.
	typedef typename property_map<Graph, edge_color_t>::const_type ColorMap;
	typedef typename graph_traits<Graph>::edge_iterator eit;
	eit it, end;
	ColorMap colors = get(edge_color, g);
	for (int i = 0; i<n_colors; ++i) {
		Z[i].setName(("z" + std::to_string(i)).c_str());
	}
	//modelling objective function
	IloExpr exp(env);
	for (int i = f_colors; i < n_colors; ++i) {
		exp += Z[i];
	}
	mod.add(IloMinimize(env, exp));
	exp.end();
	//first constraint relaxed add by cuts
	// new constraint (4.4)CCut strength tree search
	IloExpr exptreecut(env);
	std::tie(it, end) = edges(g);
	while (it != end) {
		exptreecut += Z[colors[*it]];
		++it;
	}
	int N = num_vertices(g) - 1;
	mod.add(exptreecut >= N);
	exptreecut.end();
	//second constraint
	IloExpr texp(env);
	for (int i = 0; i < f_colors; ++i) {
		texp += Z[i];
	}
	mod.add(texp <= k);
	texp.end();

}




int main()
{
	enum { A, B, C, D, E, F, G, H };
	typedef std::pair<int, int> Edge;
	graph_t::edge_iterator it, end;
	const int n_vertices = 14;
	const int k = 4;
	Edge edge_array[] = {
		Edge(1,2),  Edge(1,12), Edge(2,3),  Edge(3,4),
		Edge(4,5),  Edge(5,6),  Edge(5,8),  Edge(5,9),
		Edge(5,11), Edge(5,13), Edge(6,7),  Edge(7,8),
		Edge(8,9),  Edge(9,10), Edge(10,11),Edge(11,12),
		Edge(12,13),
	};
	int n_edges = sizeof(edge_array) / sizeof(edge_array[0]);
	const int colors[] = { H,H,D,D,C,F,E,D,C,F,G,E,A,B,G,A,B };

	graph_t g(edge_array, edge_array + n_edges, colors, n_vertices);
	//add edges to super source vertex index 0. remember!!!
	std::unordered_set<int> st(colors, colors + sizeof(colors) / sizeof(colors[0]));
	int n_colors = st.size();
	st.clear();
	for (int i = 1; i < n_vertices; ++i) boost::add_edge(0, i, property<edge_color_t, int>(n_colors + i - 1), g);
	std::tie(it, end) = boost::edges(g);
	print_edges(it, end, g);


	//temporario contar numero de cores
	n_colors += n_vertices - 1;


	//starting cplex code part
	IloEnv   env; //environment
	try {
		IloModel model(env);
		IloBoolVarArray Z(env, n_colors);
		buildCCutModel(model, Z, k, g);
		IloCplex cplex(model);
		cplex.exportModel("kSLF_CCut_relaxed.lp"); // good to see if the model is correct
											//cross your fingers

		//cuts

		cplex.use(MyCuts(env,Z,g));
	    cplex.use(LazyCallback(env,Z,g));

		//paramenters
		cplex.setParam(IloCplex::Param::MIP::Display,5);
		cplex.setParam(IloCplex::Param::Tune::Display,3);
		cplex.setParam(IloCplex::Param::Simplex::Display, 2);
		cplex.setParam(IloCplex::Param::Preprocessing::Presolve, 0);
		cplex.solve();
		cplex.out() << "solution status = " << cplex.getStatus() << endl;

		cplex.out() << endl;
		cplex.out() << "Number of components of original problem  = " << cplex.getObjValue() << endl;
		for (int i = 0; i < Z.getSize(); i++) {
			cplex.out() << "  Z" << i << " = " << cplex.getValue(Z[i]) << endl;
		}

	}
	catch (IloException& e) {
		cerr << "Concert exception caught: " << e << endl;
	}
	catch (...) {
		cerr << "Unknown exception caught" << endl;
	}
	//memory cleaning
	env.end();

	return 0;
}
