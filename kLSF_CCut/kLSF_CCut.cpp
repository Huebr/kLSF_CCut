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
#include <boost/algorithm/string/classification.hpp>
#include <boost/algorithm/string/trim.hpp>
#include <boost/graph/filtered_graph.hpp>
#include <boost/exception/all.hpp>
#include <boost/random.hpp>
#include <exception>
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
	
	boost::random::mt19937 rng;
						// see pseudo-random number generators
	// distribution that maps to 1..6
	// see random number distributions
	while (num_c_best >= 2 ) {//peharps temp.count() < k_sup
		/*boost::random::uniform_int_distribution<> gen(0, size-1);
		int i = gen(rng);
		if (!temp.test(i))temp.set(i);
		*/
		int diff;
		int best_label = -1;// produces randomness out of thin air	
		int best_diff = num_vertices(g);
		no = num_c_best;
		for (int i = 0; i <= z.getSize(); ++i) {
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
	while (num_c_best == 1) {
		int diff;
		int best_label = -1;
		int best_diff = num_vertices(g);
		no = num_c_best;
		for (int i = 0; i <= z.getSize(); ++i) {
			if (temp.test(i)) {
				temp.flip(i);
				num_c_best = get_components(g, temp, components);
				diff = num_c_best - no;
				if (diff<best_diff) {
					best_diff = diff;
					best_label = i;
				}
				if (diff > 0) {
					best_diff = diff;
					best_label = i;
					temp.set(i);
					break;
				}
				temp.set(i);
			}
		}
		if (best_label >= 0)temp.flip(best_label);
		num_c_best = get_components(g, temp, components);
	}
	if (num_c_best > 1) {
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
		while (it != end) {
			if (components[source(*it,g)]!=components[target(*it, g)]) {
				if (components[source(*it, g)] == 0 || components[target(*it, g)] == 0) {
					temp1.set(colors[*it]);
				}
			}
			++it;
		}
		for (int i = 0; i < z.getSize(); ++i) if(temp1.test(i))expr += z[i];
		addLocal(expr >= 1).end();
		expr.end();
	}
	//else std::cout << "found optimal" << std::endl;
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
	mod.add(texp == k);
	texp.end();
	IloExpr nexp(env);
	for (int i = f_colors; i < n_colors; ++i) {
		nexp += Z[i];
	}
	mod.add(nexp>=1);//setar para 1
	nexp.end();
}



template<class Graph>
void solveModel(int n_vertices, int n_colors, int k, Graph &g) {
	//starting cplex code part
	IloEnv   env; //environment
	try {
		IloModel model(env);
		IloBoolVarArray Z(env, n_colors);
		buildCCutModel(model, Z, k, g);
		IloCplex cplex(model);
		//cplex.exportModel("kSLF_CCut_relaxed.lp"); // good to see if the model is correct
												   //cross your fingers

												   //cuts

		cplex.use(MyDFSCuts(env, Z, g));
		//cplex.use(MyNewCuts(env, Z, g));
		cplex.use(LazyCallback(env, Z,k, g));

		//paramenters
		//cplex.setParam(IloCplex::Param::MIP::Display, 5);
		//cplex.setParam(IloCplex::Param::Tune::Display, 3);
		//cplex.setParam(IloCplex::Param::Simplex::Display, 2);
		cplex.setParam(IloCplex::Param::Preprocessing::Presolve, 0);
		cplex.setParam(IloCplex::Param::Parallel, -1);
		cplex.setParam(IloCplex::Param::Threads,4);// n threads
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
				std::tie(it, end) = boost::edges(g);
				//print_edges(it, end, g);
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


