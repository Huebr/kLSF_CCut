#include <iostream>                  // for std::cout
#include <utility>                   // for std::pair
#include <algorithm>                 // for std::for_each
#include <boost/graph/graph_traits.hpp> // for creation of descriptors vertex and edges.
#include <boost/graph/adjacency_list.hpp> //for usage of adjacency list
#include <boost/graph/graphml.hpp>
#include <boost/graph/connected_components.hpp>
#include <ilcplex/ilocplex.h>
#include <boost/dynamic_bitset.hpp>
#include <boost/program_options.hpp>
#include <boost/algorithm/string/split.hpp>
#include <boost/pending/disjoint_sets.hpp>
#include <boost/graph/incremental_components.hpp>
#include <boost/graph/copy.hpp>
#include <boost/algorithm/string/classification.hpp>
#include <boost/algorithm/string/trim.hpp>
#include <boost/graph/filtered_graph.hpp>
#include <boost/exception/all.hpp>
#include <boost/random.hpp>
#include <exception>
#include <queue>
#include <set>
#include <vector>
ILOSTLBEGIN //initialization make vs work properly

using namespace boost;
namespace po = boost::program_options;

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
int root(int current, std::vector<int> &parent) {
	while (parent[current] != current) {
		current = parent[current];
	}
	return current;
}


template<class Graph>
int max_reduce(Graph &g, int n_curr, int n_colors, std::vector<int> &comp, int label) {
	std::vector<int> parent(n_curr), level(n_curr);
	volatile int comp_a, comp_b; //so i could debug dont know why.
	int result;
	for (int i = 0; i < n_curr; ++i) {
		parent[i] = i;
		level[i] = 0;
	}
	result = 0;

	typedef typename property_map<Graph, edge_color_t>::type EdgeColorMap;
	typedef filtered_graph<Graph, valid_edge_color<EdgeColorMap, db> > fg;
	typedef typename fg::edge_iterator eit;
	eit it, end;
	db mask(n_colors);
	mask.set(label);
	valid_edge_color<EdgeColorMap, db> filter(get(edge_color, g), mask);
	fg G(g, filter);
	std::tie(it, end) = boost::edges(G);

	while (it != end) {
		comp_a = comp[source(*it, G)];
		comp_b = comp[target(*it, G)];
		if (comp_a != comp_b) {
			volatile int root_a, root_b;
			root_a = root(comp_a, parent);
			root_b = root(comp_b, parent);
			if (root(comp_a, parent) != root(comp_b, parent)) {
				if (level[root(comp_a, parent)] > level[root(comp_b, parent)]) parent[root(comp_b, parent)] = root(comp_a, parent);
				else {
					if (level[root(comp_a, parent)] == level[root(comp_b, parent)]) {
						level[root(comp_b, parent)]++;
					}
					parent[root(comp_a, parent)] = root(comp_b, parent);
				}
				result++;
			}
		}
		++it;
	}
	return result;
}


// need to think
ILOBRANCHCALLBACK3(MyBranchStrategy, IloBoolVarArray, z,int,k, graph_t&, g) {
	if (hasIncumbent()) {
		int n_colors = z.getSize();
		int f_colors = n_colors - num_vertices(g) + 1;// trying to pick original colors
		db mask_curr(n_colors);
		for (int i = 0; i < f_colors; ++i) {
			volatile float ub = getUB(z[i]);
			volatile float lb = getLB(z[i]);
			if (std::abs(ub - lb) <= 1e-3&&std::abs(ub - 1.0f) <= 1e-3) {//verify if is fixed by analisys of bounds verify if need to use float tolerance
				mask_curr.set(i);
			}
		}
		std::vector<int> components(num_vertices(g));// components graph
		int n_curr = get_components(g, mask_curr, components); //number of components original graph
		int n_opt = getIncumbentObjValue();
		int max = 0;
		//max reduce evaluation
		volatile int num_undecided_colors = k - mask_curr.count();
		if (num_undecided_colors > 0) {
			std::vector<int> tmp(f_colors);
			for (int i = 0; i < f_colors; ++i) { // need to consider all labels undecided
				if (!mask_curr.test(i)) {// if color i not set in test
					max = max_reduce(g, n_curr, n_colors, components, i);
					tmp.push_back(max);
				}
			}
			std::sort(tmp.begin(), tmp.end(), std::greater<int>());
			max = 0;
			for (int i = 0; i < num_undecided_colors; ++i) {
				max += tmp[i];
			}
		}
		if ((n_curr - max) >= n_opt + 1) {
			prune();
		}
	}
}


ILOUSERCUTCALLBACK2(MyNewCuts, IloBoolVarArray, z, graph_t&, g) {
	int size = z.getSize();
	db temp(size);
	std::vector<int> components(num_vertices(g));
	auto colors = get_colors(g);
	graph_traits<graph_t>::edge_iterator it, end;
	for (int i = 0; i < size; ++i) { //using colors of original graph
		if (getValue(z[i])>0) temp.set(i);
	}
	//std::cout << " user cutting" << std::endl;
	int no = get_components(g, temp, components);
	int num_c_best = no;
	
	//boost::random::mt19937 rng;
						// see pseudo-random number generators
	// distribution that maps to 1..6
	// see random number distributions
	int best_label = -1;// produces randomness out of thin air	
	while (num_c_best >= 2 && temp.count()< z.getSize()) {//peharps temp.count() < k_sup
		/*boost::random::uniform_int_distribution<> gen(0, size-1);
		int i = gen(rng);
		if (!temp.test(i))temp.set(i);
		*/
		int diff;
		int best_diff = num_vertices(g);
		no = num_c_best;
		best_label = -1;
		for (int i = 0; i < z.getSize(); ++i) {
			if (!temp.test(i)) {
				temp.set(i);
				num_c_best = get_components(g, temp, components);
				diff = no- num_c_best;
				if (diff<best_diff) {
					best_diff = diff;
					best_label = i;
					temp.flip(i);
					break;
				}
				temp.flip(i);
			}
		}
		if (best_label >= 0)temp.set(best_label);
		num_c_best = get_components(g, temp, components);
	}
	if (best_label >= 0)temp.flip(best_label);
	num_c_best = get_components(g, temp, components);
	if (num_c_best > 1) {
		//std::cout << "add user cut" << std::endl;
		//db temp1(size);
		std::tie(it, end) = edges(g);
		IloExpr expr(getEnv());
		vector<db> masks(num_c_best);
		for (int i = 0; i < num_c_best; ++i) masks[i].resize(size);
		while (it != end) {
			if (components[source(*it, g)] != components[target(*it, g)]) {
				masks[components[source(*it, g)]].set(colors[*it]);
				masks[components[target(*it, g)]].set(colors[*it]);
			}
			++it;
		}
		for (int i = 0; i < num_c_best; ++i) {
			for (int j = 0; j < z.getSize(); ++j) if (masks[i].test(j))expr += z[j];
			add(expr >= 1,IloCplex::UseCutFilter);
			expr.clear();
		}
		expr.end();
	}


}
//Callbacks new to me new to you let god save my soul

ILOUSERCUTCALLBACK2(MyDFSCuts, IloBoolVarArray, z, graph_t&, g) {
	int size = z.getSize();
	db temp(size);
	std::vector<int> components(num_vertices(g));
	auto colors = get_colors(g);
	graph_traits<graph_t>::edge_iterator it, end;
	for (int i = 0; i < size; ++i) { //using colors of original graph
		if (getValue(z[i])>0) temp.set(i);
	}
	//std::cout << " user cutting" << std::endl;
	int num_c = get_components(g, temp, components);
	if (num_c > 1) {
		//std::cout << "add user cut" << std::endl;
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
		//std::cout <<std::endl<< (expr >= 1) << std::endl;
		add(expr >= 1).end();
		expr.end();
	}
	//else std::cout << "is good" << std::endl;
}



ILOLAZYCONSTRAINTCALLBACK3(LazyCallback, IloBoolVarArray,z,int,k,graph_t&,g) {
	int size = z.getSize();
	db temp(size);
	int n_vertices = num_vertices(g);
	int f_colors = size - n_vertices + 1;
	std::vector<int> components(n_vertices);
	auto colors = get_colors(g);
	graph_traits<graph_t>::edge_iterator it, end;
	for (int i = 0; i < size  ; ++i) { //using colors of original graph
		if (std::abs(getValue(z[i])-1)<=1e-3) temp.set(i);
	}
	//std::cout << "lazy cutting"<<std::endl;
	//if (temp.count() < k)std::cout <<std::endl << "invalid number of colors" << std::endl;
	int num_c = get_components(g,temp,components);
	if (num_c > 1) {

		//std::cout << "add cut" << std::endl;
		db temp1(size);
		std::tie(it,end) = edges(g);
		IloExpr expr(getEnv());
		vector<db> masks(num_c);
		for (int i = 0; i < num_c; ++i) masks[i].resize(size);
		while (it != end) {
			if (components[source(*it,g)]!=components[target(*it, g)]) {
					masks[components[source(*it, g)]].set(colors[*it]);
					masks[components[target(*it, g)]].set(colors[*it]);
			}
			++it;
		}
		for (int i = 0; i < num_c; ++i) {
			for (int j = 0; j < z.getSize(); ++j) if (masks[i].test(j))expr += z[j];
			addLocal(expr >= 1);
			expr.clear();
		}
		expr.end();
	}
	//else std::cout << "found optimal" << std::endl;
}

//MVCA modified always has k colors
template <class Graph>
int kLSFMVCA(Graph &g, int k_sup, int n_labels) {
	std::vector<int> components(num_vertices(g));
	db temp(n_labels);
	int num_c = get_components(g, temp, components);
	int num_c_best = num_c;
	while (temp.count() < k_sup) {
		int best_label = 0;
		for (int i = 0; i < n_labels; ++i) {
			if (!temp.test(i)) {
				temp.set(i);
				int nc = get_components(g, temp, components);
				if (nc <= num_c_best) {
					num_c_best = nc;
					best_label = i;
				}
				temp.flip(i);
			}
		}
		temp.set(best_label);
	}
	num_c_best = get_components(g, temp, components);
	//print_filtered_graph(g,temp);
	return  num_c_best;//just to be right
}
//CGA
template <class Graph>
int kLSFCGA(Graph &g, int k_sup, int n_labels,int alfa, double beta) {
	std::vector<int> components(num_vertices(g));
	std::queue<int> selected_colors;
	db temp(n_labels);
	int num_c = get_components(g, temp, components);
	int num_c_best = num_c;
	int k_beta = (1.0f - beta)*k_sup;
	//phase 1
	for (int i = 0; i <= alfa * k_sup; ++i) {
		while (temp.count() < k_beta) {
			int best_label = 0;
			for (int i = 0; i < n_labels; ++i) {
				if (!temp.test(i)) {
					temp.set(i);
					int nc = get_components(g, temp, components);
					if (nc <= num_c_best) {
						num_c_best = nc;
						best_label = i;
					}
					temp.flip(i);
				}
			}
			temp.set(best_label);
			selected_colors.push(best_label);
		}
		temp.flip(selected_colors.front());
		selected_colors.pop();
	}
	while (temp.count() < k_sup) {
		int best_label = 0;
		for (int i = 0; i < n_labels; ++i) {
			if (!temp.test(i)) {
				temp.set(i);
				int nc = get_components(g, temp, components);
				if (nc <= num_c_best) {
					num_c_best = nc;
					best_label = i;
				}
				temp.flip(i);
			}
		}
		temp.set(best_label);
	}
	num_c_best = get_components(g, temp, components);
	//print_filtered_graph(g, temp);
	return  num_c_best;//just to be right
}

// preprocessing functions
template<class Graph>
void treefy(Graph& g, int n_colors) {
	Graph result(num_vertices(g));
	typedef boost::graph_traits<Graph>::edge_descriptor edge_t;
	typedef typename property_map<Graph, edge_color_t>::type EdgeColorMap;
	typedef filtered_graph<Graph, valid_edge_color<EdgeColorMap, db> > fg;
	typedef typename fg::edge_iterator eit;
	eit it, end;
	for (int l = 0; l < n_colors; ++l) {
		db mask(n_colors);
		mask.set(l);
		std::vector<int> components(num_vertices(g));// components graph
		int n_curr = get_components(g, mask, components);
		std::vector<int> my_mapping(n_curr, -1);
		for (int u = 0; u < num_vertices(g); ++u) {
			if (my_mapping[components[u]] == -1)my_mapping[components[u]] = u;
			else add_edge(my_mapping[components[u]], u, property<edge_color_t, int>(l), result);
		}
	}
	g.clear();
	copy_graph(result, g);
}
template<class Graph>
void completefy(Graph& g, int n_colors) {
	Graph result(num_vertices(g));
	typedef boost::graph_traits<Graph>::edge_descriptor edge_t;
	typedef typename property_map<Graph, edge_color_t>::type EdgeColorMap;
	typedef filtered_graph<Graph, valid_edge_color<EdgeColorMap, db> > fg;
	typedef typename fg::edge_iterator eit;
	eit it, end;
	for (int l = 0; l < n_colors; ++l) {
		db mask(n_colors);
		mask.set(l);
		std::vector<int> components(num_vertices(g));// components graph
		int n_curr = get_components(g, mask, components);
		std::vector<int> my_mapping(n_curr, -1);
		for (int u = 0; u < num_vertices(g); ++u) {
			for (int v = u + 1; v < num_vertices(g); ++v) {
				if (components[u] == components[v]) {
					add_edge(u, v, property<edge_color_t, int>(l), result);
				}
			}
		}
	}
	g.clear();
	copy_graph(result, g);
}
// preprocessing functions
template<class Graph>
void MCR(Graph& g, int n_colors) {
	Graph result(num_vertices(g));
	typedef boost::graph_traits<Graph>::edge_descriptor edge_t;
	typedef typename property_map<Graph, edge_color_t>::type EdgeColorMap;
	typedef filtered_graph<Graph, valid_edge_color<EdgeColorMap, db> > fg;
	typedef typename fg::edge_iterator eit;
	eit it, end;
	for (int l = 0; l < n_colors; ++l) {
		db mask(n_colors);
		mask.set(l);
		valid_edge_color<EdgeColorMap, db> filter(get(edge_color, g), mask);
		fg H(g, filter);
		typedef typename property_map<fg, vertex_index_t>::type IndexMap;
		IndexMap index = get(vertex_index, H);
		//disjoint_sets ds(num_vertices(g))
		typedef std::map<int, std::size_t> rank_t; // => order on Element
		typedef std::map<int, int> parent_t;
		rank_t rank_map;
		parent_t parent_map;
		boost::associative_property_map<rank_t>   rank_pmap(rank_map);
		boost::associative_property_map<parent_t> parent_pmap(parent_map);
		boost::disjoint_sets<
			associative_property_map<rank_t>,
			associative_property_map<parent_t> > ds(
				rank_pmap,
				parent_pmap);
		//std::vector<Element> elements;
		//elements.push_back(Element(...));
		//rank_t rank_map;
		//parent_t parent_map;

		//boost::associative_property_map<rank_t>   rank_pmap(rank_map);
		//boost::associative_property_map<parent_t> parent_pmap(parent_map);

		for (int i = 0; i < num_vertices(g); ++i) {
			ds.make_set(i);
		}
		std::tie(it, end) = edges(H);
		while (it != end) {
			int u = index[source(*it, H)];
			int v = index[target(*it, H)];
			if (ds.find_set(u) != ds.find_set(v)) {
				add_edge(u, v, property<edge_color_t, int>(l), result);
				ds.union_set(u, v);
			}
			else {
				std::cout << "MCR removed edge:" << " (" << u << "," << v << ") " << " Color: " << l << std::endl;
			}
			++it;
		}
	}
	g.clear();
	copy_graph(result,g);
}


template<class Graph>
void buildCCutModel(IloModel mod,IloBoolVarArray Z, int k, Graph &g) {
	IloEnv env = mod.getEnv();
	int n_colors = Z.getSize();
	int f_colors = n_colors - num_vertices(g) + 1;
	//setting names to labels variables.
	typedef typename property_map<Graph, edge_color_t>::type ColorMap;
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
	mod.add(texp == k);
	texp.end();
	IloExpr nexp(env);
	for (int i = f_colors; i < n_colors; ++i) {
		nexp += Z[i];
	}
	nexp.end();
}



template<class Graph>
void solveModel(int n_vertices, int n_colors, int k, Graph &g) {
	//starting cplex code part
	IloEnv   env; //environment
	try {
		IloModel model(env);
		IloBoolVarArray Z(env, n_colors);
		IloNumArray pri(env,n_colors);
		buildCCutModel(model, Z, k, g);
		IloCplex cplex(model);
		//cplex.exportModel("kSLF_CCut_relaxed.lp"); // good to see if the model is correct
												   //cross your fingers
		{//set priorities number edges by color.
			auto it = boost::edges(g).first;
			auto end = boost::edges(g).second;
			auto colormap = get(edge_color, g);
			while (it != end) {
				pri[colormap[*it]]++;
				++it;
			}	
		}								   //cuts

		//cplex.use(MyDFSCuts(env, Z, g));
		cplex.use(MyNewCuts(env, Z, g));
		cplex.use(LazyCallback(env, Z,k, g));
		cplex.use(MyBranchStrategy(env,Z,k,g));

		//paramenters
		//cplex.setParam(IloCplex::Param::MIP::Display, 5);
		//cplex.setParam(IloCplex::Param::Tune::Display, 3);
		//cplex.setParam(IloCplex::Param::Simplex::Display, 2);
		cplex.setParam(IloCplex::Param::Preprocessing::Presolve, 0);
		cplex.setParam(IloCplex::Param::Emphasis::MIP, 1);
		cplex.setParam(IloCplex::Param::MIP::Tolerances::LowerCutoff, 1);
		cplex.setParam(IloCplex::Param::MIP::Tolerances::UpperCutoff, kLSFMVCA(g,k,n_colors) - 1);
		//cplex.setParam(IloCplex::Param::Parallel, -1);
		cplex.setParam(IloCplex::Param::Threads,8);// n threads
		//TODO add MIP start
		// add set limit time
		cplex.setParam(IloCplex::TiLim, 7300);
		//set priorities to colors with more edges.
		cplex.setPriorities(Z,pri);

		cplex.solve();
		cplex.out() << "solution status = " << cplex.getStatus() << endl;
		db temp(n_colors);
		cplex.out() << endl;
		cplex.out() << "Number of components of original problem  = " << cplex.getObjValue() << endl;
		cplex.out() << "color(s) solution:";
		for (int i = 0; i < Z.getSize()-n_vertices + 1; i++) {
			if (std::abs(cplex.getValue(Z[i]) - 1) <= 1e-3) {
				cplex.out() << "  " << i;
				temp.set(i);
			}
		}
		cplex.out() << std::endl;
		print_filtered_graph(g, temp);
	}
	catch (IloException& e) {
		std::cerr << "Concert exception caught: " << e << endl;
	}
	catch (...) {
		std::cerr << "Unknown exception caught" << endl;
	}
	//memory cleaning
	env.end();
	
}


int main(int argc, const char *argv[])
{
	typedef adjacency_list<vecS, vecS, undirectedS, no_property, property<edge_color_t, int>> Graph;
	typedef std::pair<int, int> Edge;
	typedef boost::graph_traits<Graph>::vertex_descriptor vertex_t;
	Graph::edge_iterator it, end;
	Graph g;
	int n_vertices, n_colors;
	//command-line processor

	try {
		std::ifstream ifn;
		po::options_description desc{ "Options" };
		desc.add_options()("help,h", "produce help message")
			("input-file,i", po::value< string >(), "input file")
			("include-path,I", po::value< string >(), "include path")
			("setup-file", po::value< string >(), "setup file");
		po::positional_options_description p;
		p.add("input-file", -1);


		po::variables_map vm;
		po::store(po::command_line_parser(argc, argv).
			options(desc).positional(p).run(), vm);
		po::notify(vm);

		if (vm.count("help")) {
			cout << desc << "\n";
			return 1;
		}
		else if (vm.count("input-file"))
		{
			std::cout << "Input files are: " << vm["input-file"].as<string>() << "\n";
			if (vm.count("include-path")) {
				ifn.open((vm["include-path"].as<string>() + vm["input-file"].as<string>()).c_str(), ifstream::in);
				std::cout << "Include Path is " << vm["include-path"].as<string>() << "\n";
			}
			else ifn.open(vm["input-file"].as<string>().c_str(), ifstream::in);
			if (!ifn.is_open()) {
				std::cout << "error opening file" << std::endl;
				exit(EXIT_FAILURE);
			}
			dynamic_properties dp;
			dp.property("color", get(edge_color, g));
			read_graphml(ifn, g, dp);

			vector<string> vecI;
			split(vecI, vm["input-file"].as<string>(), is_any_of("-."), token_compress_off);
			if (vecI.size() == 6) {
				std::cout <<"n_vertices:"<< vecI[0] << std::endl;
				n_vertices = stoi(vecI[0]);
				std::cout << "n_colors:" << vecI[2] << std::endl;
				n_colors = stoi(vecI[2]);
				std::cout << "k:" << vecI[3] << std::endl;
				int k = stoi(vecI[3]);
				//add edges to super source vertex. remember!!!
				vertex_t u = add_vertex(g);
				n_vertices++;
				for (int i = 0; i < n_vertices - 1; ++i) boost::add_edge(u, i, property<edge_color_t, int>(n_colors++), g);
				//boost::add_edge(95, 76, property<edge_color_t, int>(n_colors++), g)
				//std::tie(it, end) = boost::edges(g);
				//print_edges(it, end, g);
				//MCR(g,n_colors);
				solveModel(n_vertices, n_colors, k, g);
			}
			else {
				std::cout << "file wrong name format." << std::endl;
			}

		}
		else if (vm.count("setup-file")) {
			std::cout << "Not implemented yet" << std::endl;
		}
		else {
			std::cout << "see options(-h)." << std::endl;
		}


	}
	catch (const po::error &ex) {
		std::cout << ex.what();
		exit(EXIT_FAILURE);
	}
	catch (boost::exception &ex) {
		std::cout << boost::diagnostic_information(ex) << std::endl;
	}
	catch (std::exception &ex) {
		std::cout << ex.what();
		exit(EXIT_FAILURE);
	}

	return 0;
}


