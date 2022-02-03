// temporalBH.cpp : This file contains the 'main' function. Program execution begins and ends there.


#include <iostream>
#include <iomanip>
#include <fstream>
#include <ctime>
#include <cstdint>
#include <cstdlib>
#include <numeric>
#include <string>
#include <list>
#include <vector>
#include <tuple>
#include <algorithm>
#include <iterator>
#include <chrono>
#include <typeinfo>
#include <unordered_set>
#include <unordered_map>
#include <climits>
#include <math.h>
#include <thread>
#include <chrono>
using namespace std;

//#include <vld.h> // detect momory leak for debugging

/*header files in the Boost library: https://www.boost.org/ */
#include <boost/random.hpp>
boost::random::mt19937 boost_random_time_seed{ static_cast<std::uint32_t>(std::time(0)) };


/*some header files*/
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_minimum_spanning_tree.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_Fast_GW_Growing_tree.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_generate_random_query_state_graph.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_read_graph_with_weight.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_save_graph_with_weight.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_connected_components.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_General_Pruning_tree.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_General_Pruning_forest.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_generate_random_graph.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_graph1_is_in_graph2.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_copy_weights_of_graph1_to_graph2.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_extract_subgraph.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_extract_subgraph_for_a_hash_of_vertices.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_extract_subgraph_for_a_list_of_vertices.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_random_spanning_tree.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_copy_graph_to_another_graph.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_breadth_first_search_a_tree.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_breadth_first_search_a_fixed_depth_of_vertices.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_breadth_first_search_a_fixed_number_of_vertices_in_unconnected_graphs_start_from_maxcpn.h>
#include <text mining/parse_string.h>
#include <text mining/parse_substring_between_pairs_of_delimiters.h>
#include <copy_items.h>
#include <math/ysgraph_math.h>
#include <print_items.h>
#include <text mining/string_is_number.h>
#include <ThreadPool.h>
#include <graph_v_of_v_idealID/graph_v_of_v_idealID.h>
#include <graph_v_of_v_idealID/graph_v_of_v_idealID_connected_components.h>
#include <graph_v_of_v_idealID/graph_v_of_v_idealID_Fast_GW_Growing_tree.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_to_graph_v_of_v_idealID.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_update_vertexIDs.h>


/*the ID of time i is time_ID_start + i;

time_ID must be smaller than INT_MAX;

Do not change time_ID_start in the code, it's not thread safe!

time_ID_start must be larger than vertex IDs, otherwise time ID is not unique */
int time_ID_start = 1e8;



/*some basic functions*/

#pragma region
double net_weight_PCSTPTG_single_bump(graph_hash_of_mixed_weighted& solu_tree, pair<int, int>& solu_time_interval,
	graph_hash_of_mixed_weighted& query_state_graph, double alpha) {

	/*query_state_graph contains all time_IDs and all vertices;

	solution: <tree, time_subinterval>;

	this function returns the net-weight of a solution to a PCSTPTG instance transformed from a temporal bump hunting instance;

	time complexity O(V_solu + total query times of V_solu), this is O(V_solu * m) in the worst case*/

	if (solu_tree.hash_of_vectors.size() == 0) {
		return -(solu_time_interval.second - solu_time_interval.first + 1);
	}

	double net_weight = 0;

	/*count vertex prize; time complexity O(V_solu + total query times of V_solu)*/
	for (auto it = solu_tree.hash_of_vectors.begin(); it != solu_tree.hash_of_vectors.end(); it++) {
		int v = it->first;
		auto search = query_state_graph.hash_of_hashs.find(v);
		if (search != query_state_graph.hash_of_hashs.end()) {
			for (auto it2 = search->second.begin(); it2 != search->second.end(); it2++) {
				int time_ID = it2->first; // v is queried in time_ID
				if (time_ID >= solu_time_interval.first && time_ID <= solu_time_interval.second) { // time_ID is in solution.second
					net_weight = net_weight + alpha + 1; // all transformed vertex prizes are alpha+1 or 0
				}
			}
		}
		else {
			auto search2 = query_state_graph.hash_of_vectors.find(v);
			if (search2 != query_state_graph.hash_of_vectors.end()) { // v is in query_state_graph
				for (auto it2 = search2->second.adj_vertices.begin(); it2 != search2->second.adj_vertices.end(); it2++) {
					int time_ID = it2->first;
					if (time_ID >= solu_time_interval.first && time_ID <= solu_time_interval.second) { // time_ID is in solution.second
						net_weight = net_weight + alpha + 1; // all transformed vertex prizes are alpha+1 or 0
					}
				}
			}
		}
	}

	/*count edge costs; time complexity O(1); we assume that solution.first is a tree*/
	net_weight = net_weight - (solu_tree.hash_of_vectors.size() - 1) * ((double)solu_time_interval.second - (double)solu_time_interval.first + 1);

	/*count time length; time complexity O(1)*/
	return net_weight - ((double)solu_time_interval.second - (double)solu_time_interval.first + 1);

}
#pragma endregion net_weight_PCSTPTG_single_bump

#pragma region
string unique_time_subinterval_string(pair<int, int> input_time_subinterval) {

	return to_string(input_time_subinterval.first) + "_" + to_string(input_time_subinterval.second);

}
#pragma endregion unique_time_subinterval_string

#pragma region
bool sort_time_subintervals_compare(const pair<pair<int, int>, int>& i, const pair<pair<int, int>, int>& j)
{
	return i.second > j.second;  // < is from small to big; > is from big to small
}

vector<pair<pair<int, int>, int>> sorted_all_time_subintervals(pair<int, int> input_time_interval) {

	/*time complexity: O(m^2)*/
	vector<pair<pair<int, int>, int>> Phi; // set of all time sub-intervals; <<start_time_ID,end_time_ID>,sub-interval_length>

	/*time complexity: O(m^2)*/
	for (int i = input_time_interval.first; i <= input_time_interval.second; i++) {
		for (int j = i; j <= input_time_interval.second; j++) {
			Phi.push_back({ {i,j} , j - i + 1 }); // start_time_ID may equal end_time_ID
		}
	}

	/*time complexity: O(m^2 * log m^2) = O(m^2 * log m)*/
	sort(Phi.begin(), Phi.end(), sort_time_subintervals_compare); // from large to small

	return Phi;

}
#pragma endregion sorted_all_time_subintervals

#pragma region
vector<pair<pair<int, int>, int>> sorted_selected_time_subintervals(pair<int, int> input_time_interval, int h, std::unordered_set<string>& Omega3) {

	/*
	t_1 = input_time_interval.first, t_m = input_time_interval.second,
	m = input_time_interval.second - input_time_interval.first + 1,
	t_x = input_time_interval.first + x - 1 | x <= m .
	*/
	vector<pair<pair<int, int>, int>> Phi; // <<start_time_ID,end_time_ID>,sub-interval_length>
	graph_hash_of_mixed_weighted checked_intervals; // an interval in checked_intervals is edge (start,end) exists
	int m = input_time_interval.second - input_time_interval.first + 1;

	if (m == 1) {
		Phi.push_back({ {input_time_interval.first, input_time_interval.second}, 1 });
		return Phi;
	}

	int s = log2(m);

	/*check intervals in Omega1*/
	vector<pair<int, int>> Omega1;
	for (int i = s; i >= 1; i--) {
		int time_ID_change_value = pow(2, i) - 1;
		/*check intervals from t_1*/
		int subinterval_start = input_time_interval.first;
		int subinterval_end = subinterval_start + time_ID_change_value;
		while (subinterval_end <= input_time_interval.second) {
			Omega1.push_back({ subinterval_start, subinterval_end });
			graph_hash_of_mixed_weighted_add_edge(checked_intervals, subinterval_start, subinterval_end, 1);
			subinterval_start = subinterval_end;
			subinterval_end = subinterval_start + time_ID_change_value;
		}
		if (subinterval_end > input_time_interval.second) {
			subinterval_end = input_time_interval.second;
			Omega1.push_back({ subinterval_start, subinterval_end });
			graph_hash_of_mixed_weighted_add_edge(checked_intervals, subinterval_start, subinterval_end, 1);
			/*check intervals from t_m only under this if condition*/
			subinterval_start = input_time_interval.second - time_ID_change_value;
			while (subinterval_start >= input_time_interval.first) {
				Omega1.push_back({ subinterval_start, subinterval_end });
				graph_hash_of_mixed_weighted_add_edge(checked_intervals, subinterval_start, subinterval_end, 1);
				subinterval_end = subinterval_start;
				subinterval_start = subinterval_end - time_ID_change_value;
			}
			if (subinterval_start < input_time_interval.first) {
				subinterval_start = input_time_interval.first;
				Omega1.push_back({ subinterval_start, subinterval_end });
				graph_hash_of_mixed_weighted_add_edge(checked_intervals, subinterval_start, subinterval_end, 1);
			}
		}
	}

	/*check intervals in Omega2*/
	for (int i = Omega1.size() - 1; i >= 0; i--) {
		int t_x = Omega1[i].first;
		int t_y = Omega1[i].second;
		int aa = t_x;
		while (aa <= t_y) {
			graph_hash_of_mixed_weighted_add_edge(checked_intervals, t_x, aa, 1); // this may be an edge (i,i)
			aa++;
		}
		aa = t_y;
		while (aa > t_x) {
			graph_hash_of_mixed_weighted_add_edge(checked_intervals, aa, t_y, 1);
			aa--;
		}
	}

	/*check intervals in Omega3*/
	if (h > 0) {
		int target_num = h * m * log2(m);
		vector<pair<int, int>> unselected_intervals;
		for (int i = input_time_interval.first; i < input_time_interval.second; i++) {
			for (int j = i + 1; j <= input_time_interval.second; j++) { // only non-singular time subintervals are unselected
				if (graph_hash_of_mixed_weighted_contain_edge(checked_intervals, i, j) == false) {
					unselected_intervals.push_back({ i,j });
				}
			}
		}
		if (target_num > unselected_intervals.size()) {
			target_num = unselected_intervals.size();
		}
		int Omega3_selected = 0;
		while (Omega3_selected < target_num) {
			boost::random::uniform_int_distribution<> dist{ 0, int(unselected_intervals.size() - 1) }; // generating random number in [0, candidates.size()-1]
			int rand = dist(boost_random_time_seed);
			graph_hash_of_mixed_weighted_add_edge(checked_intervals, unselected_intervals[rand].first, unselected_intervals[rand].second, 1);
			Omega3.insert(unique_time_subinterval_string({ unselected_intervals[rand].first, unselected_intervals[rand].second }));
			Omega3_selected++;
			unselected_intervals.erase(unselected_intervals.begin() + rand);
		}
	}


	/*move unique time intervals in checked_intervals to Phi; time complexity: O(m log2 m)*/
	for (int i = input_time_interval.first; i <= input_time_interval.second; i++) {
		Phi.push_back({ {i,i} , 1 }); // since Omega1 contains [t_1,t_2],[t_2,t_3]..., Omega2 contains all singular time sub-intervals
	}
	for (auto it = checked_intervals.hash_of_vectors.begin(); it != checked_intervals.hash_of_vectors.end(); it++) {
		int i = it->first;
		auto search = checked_intervals.hash_of_hashs.find(i);
		if (search != checked_intervals.hash_of_hashs.end()) {
			for (auto it2 = search->second.begin(); it2 != search->second.end(); it2++) {
				int j = it2->first;
				if (i < j) { // only count non-singular time sub-intervals
					Phi.push_back({ {i,j} , j - i + 1 });
				}
			}
		}
		else {
			auto search2 = checked_intervals.hash_of_vectors.find(i);
			for (auto it2 = search2->second.adj_vertices.begin(); it2 != search2->second.adj_vertices.end(); it2++) {
				int j = it2->first;
				if (i < j) { // only count non-singular time sub-intervals 
					Phi.push_back({ {i,j} , j - i + 1 });
				}
			}
		}
	}

	/*time complexity: O(m * log m * log m)*/
	sort(Phi.begin(), Phi.end(), sort_time_subintervals_compare); // from large to small

	return Phi;

}
#pragma endregion sorted_selected_time_subintervals

#pragma region
void build_G_dash_T_i(graph_hash_of_mixed_weighted& input_graph, graph_hash_of_mixed_weighted& query_state_graph, pair<int, int> T_i, double alpha) {

	/*this function update vertex and edge weights of input_graph;

	time complexity: O(V + sum of query_states + E), at most O(mV + E)*/

	for (auto it = input_graph.hash_of_vectors.begin(); it != input_graph.hash_of_vectors.end(); it++) {
		int v = it->first;
		it->second.vertex_weight = 0; // initialize vertex weight to 0

		/*time complexity throughout the loop: O(V + sum of query_states)*/
		auto search = query_state_graph.hash_of_hashs.find(v);
		if (search != query_state_graph.hash_of_hashs.end()) {
			for (auto it2 = search->second.begin(); it2 != search->second.end(); it2++) {
				int time_ID = it2->first;
				if (time_ID >= T_i.first && time_ID <= T_i.second) {
					it->second.vertex_weight = it->second.vertex_weight + alpha + 1; // update vertex weight
				}
			}
		}
		else {
			auto search2 = query_state_graph.hash_of_vectors.find(v);
			if (search2 != query_state_graph.hash_of_vectors.end()) { // v is in query_state_graph 
				for (auto it2 = search2->second.adj_vertices.begin(); it2 != search2->second.adj_vertices.end(); it2++) {
					int time_ID = it2->first;
					if (time_ID >= T_i.first && time_ID <= T_i.second) {
						it->second.vertex_weight = it->second.vertex_weight + alpha + 1; // update vertex weight
					}
				}
			}
		}

		/*time complexity throughout the loop: O(V + E)*/
		search = input_graph.hash_of_hashs.find(v);
		if (search != input_graph.hash_of_hashs.end()) {
			for (auto it2 = search->second.begin(); it2 != search->second.end(); it2++) {
				int adj_v = it2->first;
				if (v < adj_v) {
					graph_hash_of_mixed_weighted_add_edge(input_graph, v, adj_v, T_i.second - T_i.first + 1); // update ec
				}
			}
		}
		else {
			auto search2 = input_graph.hash_of_vectors.find(v);
			for (auto it2 = search2->second.adj_vertices.begin(); it2 != search2->second.adj_vertices.end(); it2++) {
				int adj_v = it2->first;
				if (v < adj_v) {
					graph_hash_of_mixed_weighted_add_edge(input_graph, v, adj_v, T_i.second - T_i.first + 1); // update ec
				}
			}
		}
	}

}
#pragma endregion build_G_dash_T_i

#pragma region
void update_solution(pair<graph_hash_of_mixed_weighted, pair<int, int>>& Theta_M_T_M, graph_hash_of_mixed_weighted& Theta_T_i2, double& L_for_upper_bound,
	double& w_Theta_M_T_M, pair<int, int> T_i, std::unordered_set<string>& Omega3) {

	double L_T_i = 0;
	double quick_w_T_i_Theta_T_i = 0;
	for (auto it1 = Theta_T_i2.hash_of_vectors.begin(); it1 != Theta_T_i2.hash_of_vectors.end(); it1++) {
		int i = it1->first;
		double w_i = it1->second.vertex_weight;
		quick_w_T_i_Theta_T_i = quick_w_T_i_Theta_T_i + w_i;

		auto search = Theta_T_i2.hash_of_hashs.find(i);
		if (search != Theta_T_i2.hash_of_hashs.end()) {
			for (auto it2 = search->second.begin(); it2 != search->second.end(); it2++) {
				int j = it2->first;
				if (i < j) { // edge (i,j)
					double c_ij = it2->second;
					quick_w_T_i_Theta_T_i = quick_w_T_i_Theta_T_i - c_ij;
					L_T_i = L_T_i + c_ij;
				}
			}
		}
		else {
			auto search2 = Theta_T_i2.hash_of_vectors.find(i);
			for (auto it2 = search2->second.adj_vertices.begin(); it2 != search2->second.adj_vertices.end(); it2++) {
				int j = it2->first;
				if (i < j) { // edge (i,j)
					double c_ij = it2->second;
					quick_w_T_i_Theta_T_i = quick_w_T_i_Theta_T_i - c_ij;
					L_T_i = L_T_i + c_ij;
				}
			}
		}
	}
	quick_w_T_i_Theta_T_i = quick_w_T_i_Theta_T_i - ((double)T_i.second - T_i.first + 1);

	if (quick_w_T_i_Theta_T_i > w_Theta_M_T_M) {
		Theta_M_T_M.first = Theta_T_i2;
		Theta_M_T_M.second = T_i;
		w_Theta_M_T_M = quick_w_T_i_Theta_T_i;
	}

	if (L_T_i > L_for_upper_bound&& Omega3.count(unique_time_subinterval_string(T_i)) == 0) { // in the guarantee of S-MIRROR, L is only counted in Omega2, which contains Omega1
		L_for_upper_bound = L_T_i;
	}


}
#pragma endregion update_solution

#pragma region
void update_nw_ec_most_generous_way(pair<int, int>& input_time_interval, graph_hash_of_mixed_weighted& query_state_graph, graph_hash_of_mixed_weighted& input_graph, double alpha) {

	//int queried_vertex_num = 0;
	for (auto it = input_graph.hash_of_vectors.begin(); it != input_graph.hash_of_vectors.end(); it++) {
		int v = it->first;
		bool queried_once = false;
		for (int i = input_time_interval.first; i <= input_time_interval.second; i++) {
			if (graph_hash_of_mixed_weighted_contain_edge(query_state_graph, i, v)) {
				queried_once = true;
				break;
			}
		}
		if (queried_once == false) {
			it->second.vertex_weight = 0; // vertex weight is 0
		}
		else {
			//queried_vertex_num++;
			it->second.vertex_weight = alpha + 1; // vertex weight is alpha + 1
		}

		for (auto it2 = it->second.adj_vertices.begin(); it2 != it->second.adj_vertices.end(); it2++) {
			it2->second = 1; // update ec as 1
		}
	}
	//cout << "queried_vertex_num: " << queried_vertex_num << endl;

	for (auto it = input_graph.hash_of_hashs.begin(); it != input_graph.hash_of_hashs.end(); it++) {
		for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
			it2->second = 1; // update ec as 1
		}
	}
}
#pragma endregion update_nw_ec_most_generous_way

#pragma region
void check_vertex(int v, graph_hash_of_mixed_weighted& input_graph,
	std::queue<int>& degree_0_remove_vertices, std::queue<int>& degree_1_remove_vertices, std::queue<int>& degree_2_remove_vertices) {

	if (input_graph.hash_of_vectors[v].vertex_weight == 0) {
		int d = graph_hash_of_mixed_weighted_degree(input_graph, v);
		if (d == 0) {
			degree_0_remove_vertices.push(v);
		}
		else if (d == 1) {
			degree_1_remove_vertices.push(v);
		}
		else if (d == 2) {
			degree_2_remove_vertices.push(v);
		}
	}

}

string edge_string_ID(pair<int, int> new_edge) {

	if (new_edge.first < new_edge.second) {
		return to_string(new_edge.first) + "_" + to_string(new_edge.second);
	}
	else {
		return to_string(new_edge.second) + "_" + to_string(new_edge.first);
	}

}

void degree_0_1_2_test(pair<int, int>& input_time_interval, graph_hash_of_mixed_weighted& query_state_graph, graph_hash_of_mixed_weighted& input_graph, double alpha,
	graph_hash_of_mixed_weighted& special_edges_graph, unordered_map<string, pair<pair<int, int>, pair<int, int>>>& newly_merged_edges) {

	//graph_hash_of_mixed_weighted_print_size(input_graph);

	update_nw_ec_most_generous_way(input_time_interval, query_state_graph, input_graph, alpha);

	/*degree_0_1_2_test*/
	std::queue<int> degree_0_remove_vertices, degree_1_remove_vertices, degree_2_remove_vertices;
	for (auto it = input_graph.hash_of_vectors.begin(); it != input_graph.hash_of_vectors.end(); it++) {
		if (it->second.vertex_weight == 0) {
			int d = graph_hash_of_mixed_weighted_degree(input_graph, it->first);
			if (d == 0) {
				degree_0_remove_vertices.push(it->first);
			}
			else if (d == 1) {
				degree_1_remove_vertices.push(it->first);
			}
			else if (d == 2) {
				degree_2_remove_vertices.push(it->first);
			}
		}
	}

	while (degree_0_remove_vertices.size() > 0 || degree_1_remove_vertices.size() > 0 || degree_2_remove_vertices.size() > 0) {

		while (degree_0_remove_vertices.size() > 0) {
			int v = degree_0_remove_vertices.front();
			degree_0_remove_vertices.pop();
			graph_hash_of_mixed_weighted_remove_vertex(input_graph, v);
			graph_hash_of_mixed_weighted_remove_vertex(special_edges_graph, v);
		}

		while (degree_1_remove_vertices.size() > 0) {
			int leaf = degree_1_remove_vertices.front();
			degree_1_remove_vertices.pop();
			if (input_graph.hash_of_vectors[leaf].adj_vertices.size() > 0) { // leaf is a degree 1 vertex
				int adj_v = input_graph.hash_of_vectors[leaf].adj_vertices[0].first;
				graph_hash_of_mixed_weighted_remove_vertex(input_graph, leaf);
				graph_hash_of_mixed_weighted_remove_vertex(special_edges_graph, leaf);
				check_vertex(adj_v, input_graph, degree_0_remove_vertices, degree_1_remove_vertices, degree_2_remove_vertices);
			}
			else { // leaf is a degree 0 vertex
				degree_0_remove_vertices.push(leaf);
			}
		}

		while (degree_2_remove_vertices.size() > 0) {
			int j = degree_2_remove_vertices.front();
			degree_2_remove_vertices.pop();
			int degree_j = input_graph.hash_of_vectors[j].adj_vertices.size();
			if (degree_j == 2) {
				int i = input_graph.hash_of_vectors[j].adj_vertices[0].first; // we assume that two edges are stored in vectors, not in hashes
				int k = input_graph.hash_of_vectors[j].adj_vertices[1].first;
				if (graph_hash_of_mixed_weighted_contain_edge(input_graph, i, k)) {
					double c_ij = graph_hash_of_mixed_weighted_edge_weight(input_graph, i, j);
					double c_ik = graph_hash_of_mixed_weighted_edge_weight(input_graph, i, k);
					double c_jk = graph_hash_of_mixed_weighted_edge_weight(input_graph, j, k);
					graph_hash_of_mixed_weighted_remove_edge_but_not_isolated_vertices(input_graph, i, j);
					graph_hash_of_mixed_weighted_remove_edge_but_not_isolated_vertices(input_graph, j, k);
					graph_hash_of_mixed_weighted_remove_edge_and_isolated_vertices(special_edges_graph, i, j);
					graph_hash_of_mixed_weighted_remove_edge_and_isolated_vertices(special_edges_graph, j, k);
					degree_0_remove_vertices.push(j);
					if (c_ik > c_ij + c_jk) {
						graph_hash_of_mixed_weighted_add_edge(input_graph, i, k, c_ij + c_jk);
						graph_hash_of_mixed_weighted_add_edge(special_edges_graph, i, k, c_ij + c_jk);
						newly_merged_edges[edge_string_ID({ i,k })] = { {i,j},{j,k} };
					}
				}
				else {
					double c_ij = graph_hash_of_mixed_weighted_edge_weight(input_graph, i, j);
					double c_jk = graph_hash_of_mixed_weighted_edge_weight(input_graph, j, k);
					graph_hash_of_mixed_weighted_remove_edge_but_not_isolated_vertices(input_graph, i, j);
					graph_hash_of_mixed_weighted_remove_edge_but_not_isolated_vertices(input_graph, j, k);
					graph_hash_of_mixed_weighted_remove_edge_and_isolated_vertices(special_edges_graph, i, j);
					graph_hash_of_mixed_weighted_remove_edge_and_isolated_vertices(special_edges_graph, j, k);
					degree_0_remove_vertices.push(j);
					graph_hash_of_mixed_weighted_add_edge(input_graph, i, k, c_ij + c_jk);
					graph_hash_of_mixed_weighted_add_edge(special_edges_graph, i, k, c_ij + c_jk);
					newly_merged_edges[edge_string_ID({ i,k })] = { {i,j},{j,k} };
				}
				check_vertex(i, input_graph, degree_0_remove_vertices, degree_1_remove_vertices, degree_2_remove_vertices);
				check_vertex(k, input_graph, degree_0_remove_vertices, degree_1_remove_vertices, degree_2_remove_vertices);
			}
			else if (degree_j == 1) {
				degree_1_remove_vertices.push(j);
			}
			else { // j is a degree 0 vertex
				degree_0_remove_vertices.push(j);
			}
		}
	}

	//graph_hash_of_mixed_weighted_print_size(input_graph);
	//getchar();
}
#pragma endregion degree_0_1_2_test

#pragma region
graph_hash_of_mixed_weighted change_reduced_tree_to_original_tree(graph_hash_of_mixed_weighted& reduced_tree, unordered_map<string, pair<pair<int, int>, pair<int, int>>>& newly_merged_edges) {

	if (reduced_tree.hash_of_vectors.size() <= 1) { // there is no edge in reduced_tree
		return reduced_tree;
	}

	graph_hash_of_mixed_weighted original_tree;

	std::queue<pair<int, int>> unadded_edges;

	for (auto it1 = reduced_tree.hash_of_vectors.begin(); it1 != reduced_tree.hash_of_vectors.end(); it1++) {
		int i = it1->first;
		auto search = reduced_tree.hash_of_hashs.find(i);
		if (search != reduced_tree.hash_of_hashs.end()) {
			for (auto it2 = search->second.begin(); it2 != search->second.end(); it2++) {
				int j = it2->first;
				if (i < j) {
					if (newly_merged_edges.count(edge_string_ID({ i,j })) == 0) { // (i,j) is an original edge
						graph_hash_of_mixed_weighted_add_edge(original_tree, i, j, 1);
					}
					else {
						unadded_edges.push({ i,j });
					}
				}
			}
		}
		else {
			auto search2 = reduced_tree.hash_of_vectors.find(i);
			for (auto it2 = search2->second.adj_vertices.begin(); it2 != search2->second.adj_vertices.end(); it2++) {
				int j = it2->first;
				if (i < j) {
					if (newly_merged_edges.count(edge_string_ID({ i,j })) == 0) { // (i,j) is an original edge
						graph_hash_of_mixed_weighted_add_edge(original_tree, i, j, 1);
					}
					else {
						unadded_edges.push({ i,j });
					}
				}
			}
		}
	}

	while (unadded_edges.size() > 0) {
		pair<int, int> edge_pair = unadded_edges.front();
		unadded_edges.pop();
		if (newly_merged_edges.count(edge_string_ID({ edge_pair.first,edge_pair.second })) == 0) { // (i,j) is an original edge
			graph_hash_of_mixed_weighted_add_edge(original_tree, edge_pair.first, edge_pair.second, 1);
		}
		else {
			pair<pair<int, int>, pair<int, int>> e1_e2 = newly_merged_edges[edge_string_ID({ edge_pair.first,edge_pair.second })];
			unadded_edges.push(e1_e2.first);
			unadded_edges.push(e1_e2.second);
		}
	}

	return original_tree;

}
#pragma endregion change_reduced_tree_to_original_tree



/*accelerated_MIRROR and accelerated_S_MIRROR*/

#pragma region
void transform_input_graphs_and_times(pair<int, int> input_time_interval, int& time_ID_old_to_new_change_value, graph_hash_of_mixed_weighted& input_graph,
	graph_hash_of_mixed_weighted& query_state_graph, unordered_map<int, int>& vertexID_old_to_new, vector<int>& vertexID_new_to_old, graph_v_of_v_idealID& new_input_graph, graph_v_of_v_idealID& new_query_state_graph) {


	vertexID_new_to_old.resize(input_graph.hash_of_vectors.size());
	int new_v_id = 0;
	for (auto it = input_graph.hash_of_vectors.begin(); it != input_graph.hash_of_vectors.end(); it++) {
		vertexID_new_to_old[new_v_id] = it->first;
		vertexID_old_to_new[it->first] = new_v_id;
		new_v_id++;
	}
	new_input_graph = graph_hash_of_mixed_weighted_to_graph_v_of_v_idealID(input_graph, vertexID_old_to_new);

	time_ID_old_to_new_change_value = new_input_graph.size() - input_time_interval.first; // new_time starts at input_time_interval.first + time_ID_old_to_new_change_value = new_input_graph.size()

	/* vertices in new_query_state_graph starts from 0 to new_input_graph.size() + input_time_interval.second - input_time_interval.first */
	new_query_state_graph.resize(new_input_graph.size() + input_time_interval.second - input_time_interval.first + 1);
	int N = new_input_graph.size();
	for (int i = 0; i < N; i++) {
		std::vector<int> times = query_state_graph.adj_v(vertexID_new_to_old[i]);
		int size_times = times.size();
		for (int j = 0; j < size_times; j++) {
			if (times[j] >= input_time_interval.first && times[j] <= input_time_interval.second) {
				graph_v_of_v_idealID_add_edge(new_query_state_graph, i, times[j] + time_ID_old_to_new_change_value, 1);
			}
		}
	}

}
#pragma endregion transform_input_graphs_and_times

#pragma region
void accelerated_build_G_dash_T_i(graph_v_of_v_idealID& input_graph, graph_v_of_v_idealID& query_state_graph, pair<int, int> T_i, double alpha, int time_ID_old_to_new_change_value, vector<double>& vertexID_new_weights) {

	/*this function update vertex and edge weights of input_graph;

	time complexity: O(V + sum of query_states + E), at most O(mV + E)*/

	int N = input_graph.size();

	pair<int, int> new_T_i = { T_i.first + time_ID_old_to_new_change_value, T_i.second + time_ID_old_to_new_change_value };
	int delta_T_i = T_i.second - T_i.first + 1;

	for (int v = 0; v < N; v++) {
		vertexID_new_weights[v] = 0; // initialize vertex weight to 0

		/*time complexity throughout the loop: O(V + sum of query_states)*/
		int adj_size = query_state_graph[v].size();
		for (int i = 0; i < adj_size; i++) {
			int new_time_ID = query_state_graph[v][i].first;
			if (new_time_ID >= new_T_i.first && new_time_ID <= new_T_i.second) {
				vertexID_new_weights[v] = vertexID_new_weights[v] + alpha + 1; // update vertex weight
			}
		}

		/*time complexity throughout the loop: O(V + E)*/
		adj_size = input_graph[v].size();
		for (int i = 0; i < adj_size; i++) {
			input_graph[v][i].second = delta_T_i; // update ec
		}
	}

}
#pragma endregion accelerated_build_G_dash_T_i

#pragma region
bool accelerated_skip_to_next_loop(std::list<std::list<int>>& cpns, pair<int, int>& T_i, vector<double>& vertexID_new_weights,
	double& w_Theta_M_T_M, std::unordered_set<string>& P, double& kappa_2) {

	/*pruning; time complexity: O(|V|)*/
	double max_nw_sum_a_cpn = 0, max_UB_weight = -INT_MAX, Gsub_ec = (double)T_i.second - T_i.first + 1;
	for (auto it = cpns.begin(); it != cpns.end(); it++) {
		double nw_sum = 0, larger_than_ec_total_weight = 0;
		int larger_than_ec_total_num = 0;
		for (auto it2 = it->begin(); it2 != it->end(); it2++) {
			double nw = vertexID_new_weights[*it2];
			if (nw > 0) {
				nw_sum = nw_sum + nw;
				if (nw > Gsub_ec) {
					larger_than_ec_total_weight = larger_than_ec_total_weight + nw;
					larger_than_ec_total_num++;
				}
			}
		}
		if (max_nw_sum_a_cpn < nw_sum) {
			max_nw_sum_a_cpn = nw_sum;
		}
		double solu_weight_UB = -INT_MAX;
		if (larger_than_ec_total_num > 0) {
			solu_weight_UB = larger_than_ec_total_weight - (double)larger_than_ec_total_num * Gsub_ec;
		}
		if (max_UB_weight < solu_weight_UB) {
			max_UB_weight = solu_weight_UB;
		}
	}
	if (max_nw_sum_a_cpn - ((double)T_i.second - T_i.first + 1) <= w_Theta_M_T_M) {
		if (max_nw_sum_a_cpn <= w_Theta_M_T_M) {
			for (int yy = T_i.first; yy <= T_i.second; yy++) {
				for (int zz = yy; zz <= T_i.second; zz++) {
					P.insert(unique_time_subinterval_string({ yy,zz }));
				}
			}
		}
		if (kappa_2 < max_nw_sum_a_cpn) {
			kappa_2 = max_nw_sum_a_cpn;
		}
		return true;
	}
	if (max_UB_weight <= w_Theta_M_T_M) {
		if (kappa_2 < max_nw_sum_a_cpn) {
			kappa_2 = max_nw_sum_a_cpn;
		}
		return true;
	}

	return false;

}
#pragma endregion accelerated_skip_to_next_loop

#pragma region
vector<pair<pair<int, int>, double>> record_special_edges(graph_hash_of_mixed_weighted& special_edges_graph, unordered_map<int, int>& vertexID_old_to_new) {

	vector<pair<pair<int, int>, double>> special_edges;

	for (auto it1 = special_edges_graph.hash_of_vectors.begin(); it1 != special_edges_graph.hash_of_vectors.end(); it1++) {
		int i = it1->first;
		auto search = special_edges_graph.hash_of_hashs.find(i);
		if (search != special_edges_graph.hash_of_hashs.end()) {
			for (auto it2 = search->second.begin(); it2 != search->second.end(); it2++) {
				int j = it2->first;
				if (i < j) {
					double ec = it2->second;
					special_edges.push_back({ {vertexID_old_to_new[i],vertexID_old_to_new[j]},ec });
				}
			}
		}
		else {
			auto search2 = special_edges_graph.hash_of_vectors.find(i);
			for (auto it2 = search2->second.adj_vertices.begin(); it2 != search2->second.adj_vertices.end(); it2++) {
				int j = it2->first;
				if (i < j) {
					double ec = it2->second;
					special_edges.push_back({ {vertexID_old_to_new[i],vertexID_old_to_new[j]},ec });
				}
			}
		}
	}

	return special_edges;
}
#pragma endregion record_special_edges

#pragma region
void accelerated_update_special_edges_in_G_dash_T_i(vector<pair<pair<int, int>, double>>& special_edges, graph_v_of_v_idealID& G_dash_T_i, double T_i_module) {

	int special_edges_size = special_edges.size();
	for (int i = 0; i < special_edges_size; i++) {
		graph_v_of_v_idealID_add_edge(G_dash_T_i, special_edges[i].first.first, special_edges[i].first.second, special_edges[i].second * T_i_module);
	}
}
#pragma endregion accelerated_update_special_edges_in_G_dash_T_i

#pragma region
pair<graph_hash_of_mixed_weighted, pair<int, int>> accelerated_MIRROR_main_process(pair<int, int> input_time_interval, graph_hash_of_mixed_weighted& input_graph,
	graph_hash_of_mixed_weighted& query_state_graph, double alpha, double& L_for_upper_bound, vector<pair<pair<int, int>, int>>& Phi,
	std::unordered_set<string>& Omega3, graph_hash_of_mixed_weighted& special_edges_graph, double& kappa_2, bool use_B_and_B) {

	L_for_upper_bound = 0, kappa_2 = 0;

	/*initialization; time complexity: O(1)*/
	pair<graph_hash_of_mixed_weighted, pair<int, int>> Theta_M_T_M; // <tree, time_subinterval>
	double w_Theta_M_T_M = -INT_MAX;
	std::unordered_set<string> P; // the pruned time sub-interval

	/*transform input_graph and query_state_graph to graph_v_of_v_idealID*/
	int time_ID_old_to_new_change_value = 0;
	vector<int> vertexID_new_to_old;
	unordered_map<int, int> vertexID_old_to_new;
	graph_v_of_v_idealID new_input_graph, new_query_state_graph;
	transform_input_graphs_and_times(input_time_interval, time_ID_old_to_new_change_value, input_graph, query_state_graph, vertexID_old_to_new, vertexID_new_to_old, new_input_graph, new_query_state_graph);
	vector<double> vertexID_new_weights(new_input_graph.size(), 0);

	/*time complexity O(|V|+|E|)*/
	std::list<std::list<int>> cpns = graph_v_of_v_idealID_connected_components(new_input_graph);

	vector<pair<pair<int, int>, double>> special_edges = record_special_edges(special_edges_graph, vertexID_old_to_new);

	/*enumerate all time sub-intervals*/
	for (int xx = 0; xx < Phi.size(); xx++) {
		pair<int, int> T_i = Phi[xx].first;
		if (P.count(unique_time_subinterval_string(T_i)) == 0) { // T_i has not been removed

			/*time complexity: O(V + sum of query_states + E), at most O(mV + E)*/
			accelerated_build_G_dash_T_i(new_input_graph, new_query_state_graph, T_i, alpha, time_ID_old_to_new_change_value, vertexID_new_weights);

			if (use_B_and_B && accelerated_skip_to_next_loop(cpns, T_i, vertexID_new_weights, w_Theta_M_T_M, P, kappa_2)) {
				continue;
			}

			accelerated_update_special_edges_in_G_dash_T_i(special_edges, new_input_graph, (double)T_i.second - T_i.first + 1); // special edge weights are not used in the above pruning process

			/*Fast_GW_Growing; Time complexity: O(d E log V)*/
			graph_hash_of_mixed_weighted Theta_T_i = graph_v_of_v_idealID_Fast_GW_Growing_tree(new_input_graph, vertexID_new_weights, "tree");

			/*General_Pruning for trees*/
			graph_hash_of_mixed_weighted Theta_T_i2 = graph_hash_of_mixed_weighted_General_Pruning_tree(Theta_T_i);

			update_solution(Theta_M_T_M, Theta_T_i2, L_for_upper_bound, w_Theta_M_T_M, T_i, Omega3);

		}
	}

	/*change new vertex_IDs in Theta_M_T_M to old vertex IDs*/
	Theta_M_T_M.first = graph_hash_of_mixed_weighted_update_vertexIDs(Theta_M_T_M.first, vertexID_new_to_old);


	return Theta_M_T_M;
}
#pragma endregion accelerated_MIRROR_main_process

#pragma region
pair<graph_hash_of_mixed_weighted, pair<int, int>> accelerated_MIRROR(pair<int, int> input_time_interval, graph_hash_of_mixed_weighted& input_graph,
	graph_hash_of_mixed_weighted& query_state_graph, double alpha, double& L_for_upper_bound, bool use_reudction, bool use_B_and_B) {

	graph_hash_of_mixed_weighted new_input_graph = input_graph;

	vector<pair<pair<int, int>, int>> Phi = sorted_all_time_subintervals(input_time_interval);
	std::unordered_set<string> Omega3;
	double kappa_2;

	/*reduce input_graph, which is a copy here*/
	graph_hash_of_mixed_weighted special_edges_graph;
	unordered_map<string, pair<pair<int, int>, pair<int, int>>> newly_merged_edges; // string is the ID of a newly merged edge, the two pairs are the two edges that correspond to the newly merged edge
	if (use_reudction) {
		degree_0_1_2_test(input_time_interval, query_state_graph, new_input_graph, alpha, special_edges_graph, newly_merged_edges);
	}

	pair<graph_hash_of_mixed_weighted, pair<int, int>> Theta_M_T_M = accelerated_MIRROR_main_process(input_time_interval,
		new_input_graph, query_state_graph, alpha, L_for_upper_bound, Phi, Omega3, special_edges_graph, kappa_2, use_B_and_B);

	Theta_M_T_M.first = change_reduced_tree_to_original_tree(Theta_M_T_M.first, newly_merged_edges);

	return Theta_M_T_M;

}
#pragma endregion accelerated_MIRROR

#pragma region
pair<graph_hash_of_mixed_weighted, pair<int, int>> accelerated_S_MIRROR(pair<int, int> input_time_interval, graph_hash_of_mixed_weighted& input_graph,
	graph_hash_of_mixed_weighted& query_state_graph, double alpha, double& kappa_1, int& reduced_V, int h, double& kappa_2, bool use_reudction, bool use_B_and_B) {

	graph_hash_of_mixed_weighted new_input_graph = input_graph;

	std::unordered_set<string> Omega3;
	vector<pair<pair<int, int>, int>> Phi = sorted_selected_time_subintervals(input_time_interval, h, Omega3);

	/*reduce input_graph, which is a copy here*/
	graph_hash_of_mixed_weighted special_edges_graph;
	unordered_map<string, pair<pair<int, int>, pair<int, int>>> newly_merged_edges; // string is the ID of a newly merged edge, the two pairs are the two edges that correspond to the newly merged edge
	if (use_reudction) {
		degree_0_1_2_test(input_time_interval, query_state_graph, new_input_graph, alpha, special_edges_graph, newly_merged_edges);
	}

	reduced_V = new_input_graph.hash_of_vectors.size();

	pair<graph_hash_of_mixed_weighted, pair<int, int>> Theta_M_T_M = accelerated_MIRROR_main_process(input_time_interval,
		new_input_graph, query_state_graph, alpha, kappa_1, Phi, Omega3, special_edges_graph, kappa_2, use_B_and_B);

	Theta_M_T_M.first = change_reduced_tree_to_original_tree(Theta_M_T_M.first, newly_merged_edges);

	return Theta_M_T_M;

}
#pragma endregion accelerated_S_MIRROR

/*accelerated_H_MIRROR and accelerated_H_S_MIRROR*/

#pragma region
void accelerated_bfs_reduce_graph(pair<int, int>& input_time_interval, graph_hash_of_mixed_weighted& query_state_graph, graph_hash_of_mixed_weighted& input_graph, double alpha, int depth) {

	update_nw_ec_most_generous_way(input_time_interval, query_state_graph, input_graph, alpha);

	std::unordered_set<int> bfs_Vsub;
	std::unordered_map<int, int> bfs_Vsub_depth;

	for (auto it = input_graph.hash_of_vectors.begin(); it != input_graph.hash_of_vectors.end(); it++) {

		if (it->second.vertex_weight > 0) {
			std::queue<int> Q;
			Q.push(it->first);
			bfs_Vsub_depth[it->first] = 0; // the depth of root is 0

			while (Q.size() > 0) {
				int v = Q.front();
				int v_depth = bfs_Vsub_depth[v];
				Q.pop(); //Removing v from queue,whose neighbour will be visited now

				if (v_depth > depth) {
					continue;
				}
				bfs_Vsub.insert(v);

				/*processing all the neighbours of v*/
				auto search = input_graph.hash_of_hashs.find(v);
				if (search != input_graph.hash_of_hashs.end()) {
					for (auto it2 = search->second.begin(); it2 != search->second.end(); it2++) {
						int adj_v = it2->first;
						auto pointer_bfs_Vsub_depth_adj_v = bfs_Vsub_depth.find(adj_v);
						if (pointer_bfs_Vsub_depth_adj_v == bfs_Vsub_depth.end()) { // adj_v has not been searched yet
							bfs_Vsub_depth[adj_v] = v_depth + 1;
							Q.push(adj_v);
						}
						else if (pointer_bfs_Vsub_depth_adj_v->second > v_depth + 1) { // adj_v has been searched from a root more far away
							pointer_bfs_Vsub_depth_adj_v->second = v_depth + 1;
							Q.push(adj_v);
						}
					}
				}
				else {
					auto search2 = input_graph.hash_of_vectors.find(v);
					for (auto it2 = search2->second.adj_vertices.begin(); it2 != search2->second.adj_vertices.end(); it2++) {
						int adj_v = it2->first;
						auto pointer_bfs_Vsub_depth_adj_v = bfs_Vsub_depth.find(adj_v);
						if (pointer_bfs_Vsub_depth_adj_v == bfs_Vsub_depth.end()) { // adj_v has not been searched yet
							bfs_Vsub_depth[adj_v] = v_depth + 1;
							Q.push(adj_v);
						}
						else if (pointer_bfs_Vsub_depth_adj_v->second > v_depth + 1) { // adj_v has been searched from a root more far away
							pointer_bfs_Vsub_depth_adj_v->second = v_depth + 1;
							Q.push(adj_v);
						}
					}
				}

			}
		}
	}

	input_graph = graph_hash_of_mixed_weighted_extract_subgraph(input_graph, bfs_Vsub);

	//graph_hash_of_mixed_weighted_print_size(input_graph);

}
#pragma endregion accelerated_bfs_reduce_graph

#pragma region
pair<graph_hash_of_mixed_weighted, pair<int, int>> accelerated_H_MIRROR(pair<int, int> input_time_interval, graph_hash_of_mixed_weighted& input_graph,
	graph_hash_of_mixed_weighted& query_state_graph, double alpha, int depth) {

	graph_hash_of_mixed_weighted new_input_graph = graph_hash_of_mixed_weighted_copy_graph(input_graph);

	vector<pair<pair<int, int>, int>> Phi = sorted_all_time_subintervals(input_time_interval);
	std::unordered_set<string> Omega3;
	double kappa_2;

	/*bfs reduce input_graph, which is a copy here*/
	accelerated_bfs_reduce_graph(input_time_interval, query_state_graph, new_input_graph, alpha, depth);

	/*reduce input_graph, which is a copy here*/
	graph_hash_of_mixed_weighted special_edges_graph;
	unordered_map<string, pair<pair<int, int>, pair<int, int>>> newly_merged_edges; // string is the ID of a newly merged edge, the two pairs are the two edges that correspond to the newly merged edge
	degree_0_1_2_test(input_time_interval, query_state_graph, new_input_graph, alpha, special_edges_graph, newly_merged_edges);

	double L_for_upper_bound;

	pair<graph_hash_of_mixed_weighted, pair<int, int>> Theta_M_T_M = accelerated_MIRROR_main_process(input_time_interval,
		new_input_graph, query_state_graph, alpha, L_for_upper_bound, Phi, Omega3, special_edges_graph, kappa_2, true);

	Theta_M_T_M.first = change_reduced_tree_to_original_tree(Theta_M_T_M.first, newly_merged_edges);

	return Theta_M_T_M;
}
#pragma endregion accelerated_H_MIRROR

#pragma region
pair<graph_hash_of_mixed_weighted, pair<int, int>> accelerated_H_S_MIRROR(pair<int, int> input_time_interval, graph_hash_of_mixed_weighted& input_graph,
	graph_hash_of_mixed_weighted& query_state_graph, double alpha, int h, int depth) {

	graph_hash_of_mixed_weighted new_input_graph = graph_hash_of_mixed_weighted_copy_graph(input_graph);

	std::unordered_set<string> Omega3;
	vector<pair<pair<int, int>, int>> Phi = sorted_selected_time_subintervals(input_time_interval, h, Omega3);
	double kappa_2;

	/*bfs reduce input_graph, which is a copy here*/
	accelerated_bfs_reduce_graph(input_time_interval, query_state_graph, new_input_graph, alpha, depth);

	/*reduce input_graph, which is a copy here*/
	graph_hash_of_mixed_weighted special_edges_graph;
	unordered_map<string, pair<pair<int, int>, pair<int, int>>> newly_merged_edges; // string is the ID of a newly merged edge, the two pairs are the two edges that correspond to the newly merged edge
	degree_0_1_2_test(input_time_interval, query_state_graph, new_input_graph, alpha, special_edges_graph, newly_merged_edges);

	double L_for_upper_bound;

	pair<graph_hash_of_mixed_weighted, pair<int, int>> Theta_M_T_M = accelerated_MIRROR_main_process(input_time_interval,
		new_input_graph, query_state_graph, alpha, L_for_upper_bound, Phi, Omega3, special_edges_graph, kappa_2, true);

	Theta_M_T_M.first = change_reduced_tree_to_original_tree(Theta_M_T_M.first, newly_merged_edges);

	return Theta_M_T_M;

}
#pragma endregion accelerated_H_S_MIRROR




/*adapted static algorithms for hunting temporal bumps*/

#pragma region
double PCST_weight(graph_hash_of_mixed_weighted& solu_tree) {

	double total_weight = 0;

	for (auto it1 = solu_tree.hash_of_vectors.begin(); it1 != solu_tree.hash_of_vectors.end(); it1++) {
		int i = it1->first;
		double nw = it1->second.vertex_weight;
		total_weight = total_weight + nw;

		auto search = solu_tree.hash_of_hashs.find(i);
		if (search != solu_tree.hash_of_hashs.end()) {
			for (auto it2 = search->second.begin(); it2 != search->second.end(); it2++) {
				int j = it2->first;
				if (i < j) {
					double ec = it2->second;
					total_weight = total_weight - ec;
				}
			}
		}
		else {
			auto search2 = solu_tree.hash_of_vectors.find(i);
			for (auto it2 = search2->second.adj_vertices.begin(); it2 != search2->second.adj_vertices.end(); it2++) {
				int j = it2->first;
				if (i < j) {
					double ec = it2->second;
					total_weight = total_weight - ec;
				}
			}
		}
	}

	return total_weight;

}
#pragma endregion PCST_weight

#pragma region
pair<graph_hash_of_mixed_weighted, pair<int, int>> BF_ST(pair<int, int> input_time_interval, graph_hash_of_mixed_weighted& input_graph,
	graph_hash_of_mixed_weighted& query_state_graph, double alpha, int random_times) {

	std::list<std::list<int>> cpns = graph_hash_of_mixed_weighted_connected_components(input_graph);

	vector<pair<pair<int, int>, int>> Phi = sorted_all_time_subintervals(input_time_interval);

	pair<graph_hash_of_mixed_weighted, pair<int, int>> Theta_best; // <tree, time_subinterval>
	double w_Theta_best = -INT_MAX;

	graph_hash_of_mixed_weighted static_bump_best;
	double w_static_bump_best = -INT_MAX;

	update_nw_ec_most_generous_way(input_time_interval, query_state_graph, input_graph, alpha); // in input_graph, queried vertices have positive weights, while not-queried vertices have 0 weight


	for (auto it0 = cpns.begin(); it0 != cpns.end(); it0++) {

		/*find vertices queried at least once in T*/
		vector<int> queried_vertices;
		for (auto it = it0->begin(); it != it0->end(); it++) {
			int v = *it;
			bool queried_once = false;
			for (int i = input_time_interval.first; i <= input_time_interval.second; i++) {
				if (graph_hash_of_mixed_weighted_contain_edge(query_state_graph, i, v)) {
					queried_once = true;
					break;
				}
			}
			if (queried_once == true) {
				queried_vertices.push_back(v);
			}
		}

		if (queried_vertices.size() > 0) { // this cpn may be profitable

			for (int iter_time = 0; iter_time < random_times; iter_time++) {

				/*random bfs root*/
				boost::random::uniform_int_distribution<> dist{ static_cast<int>(0), static_cast<int>(queried_vertices.size() - 1) };
				int root = queried_vertices[dist(boost_random_time_seed)];

				graph_hash_of_mixed_weighted bfs_tree = graph_hash_of_mixed_weighted_breadth_first_search_a_tree(input_graph, root); // bfs_tree is a spanning tree of this cpn

				graph_hash_of_mixed_weighted Theta_T_i2 = graph_hash_of_mixed_weighted_General_Pruning_tree(bfs_tree);

				double w_Theta_T_i2 = PCST_weight(Theta_T_i2);

				if (w_Theta_T_i2 > w_static_bump_best) {
					w_static_bump_best = w_Theta_T_i2;
					static_bump_best = Theta_T_i2;
				}

			}

		}

	}

	/*find best pair of subtree of time subinterval*/
	for (int xx = 0; xx < Phi.size(); xx++) {
		pair<int, int> T_i = Phi[xx].first;

		build_G_dash_T_i(static_bump_best, query_state_graph, T_i, alpha);

		static_bump_best = graph_hash_of_mixed_weighted_General_Pruning_tree(static_bump_best);

		if (static_bump_best.hash_of_vectors.size() > 0) { // at least one vertex
			double L_for_upper_bound;
			std::unordered_set<string> Omega3;
			update_solution(Theta_best, static_bump_best, L_for_upper_bound, w_Theta_best, T_i, Omega3);
		}
	}

	return Theta_best;

}
#pragma endregion BF_ST

#pragma region
pair<graph_hash_of_mixed_weighted, pair<int, int>> Random_ST(pair<int, int> input_time_interval, graph_hash_of_mixed_weighted& input_graph,
	graph_hash_of_mixed_weighted& query_state_graph, double alpha, int random_times) {

	std::list<std::list<int>> cpns = graph_hash_of_mixed_weighted_connected_components(input_graph);

	vector<pair<pair<int, int>, int>> Phi = sorted_all_time_subintervals(input_time_interval);

	pair<graph_hash_of_mixed_weighted, pair<int, int>> Theta_best; // <tree, time_subinterval>
	double w_Theta_best = -INT_MAX;

	graph_hash_of_mixed_weighted static_bump_best;
	double w_static_bump_best = -INT_MAX;

	update_nw_ec_most_generous_way(input_time_interval, query_state_graph, input_graph, alpha); // in input_graph, queried vertices have positive weights, while not-queried vertices have 0 weight


	for (auto it0 = cpns.begin(); it0 != cpns.end(); it0++) {

		graph_hash_of_mixed_weighted cpn_graph = graph_hash_of_mixed_weighted_extract_subgraph_for_a_list_of_vertices(input_graph, *it0);

		for (int iter_time = 0; iter_time < random_times; iter_time++) {

			graph_hash_of_mixed_weighted random_tree = graph_hash_of_mixed_weighted_random_spanning_tree(cpn_graph);

			graph_hash_of_mixed_weighted Theta_T_i2 = graph_hash_of_mixed_weighted_General_Pruning_tree(random_tree);

			double w_Theta_T_i2 = PCST_weight(Theta_T_i2);

			if (w_Theta_T_i2 > w_static_bump_best) {
				w_static_bump_best = w_Theta_T_i2;
				static_bump_best = Theta_T_i2;
			}

		}

	}

	/*find best pair of subtree of time subinterval*/
	for (int xx = 0; xx < Phi.size(); xx++) {
		pair<int, int> T_i = Phi[xx].first;

		build_G_dash_T_i(static_bump_best, query_state_graph, T_i, alpha);

		static_bump_best = graph_hash_of_mixed_weighted_General_Pruning_tree(static_bump_best);

		if (static_bump_best.hash_of_vectors.size() > 0) {
			double L_for_upper_bound;
			std::unordered_set<string> Omega3;
			update_solution(Theta_best, static_bump_best, L_for_upper_bound, w_Theta_best, T_i, Omega3);
		}
	}


	return Theta_best;

}
#pragma endregion Random_ST

#pragma region
graph_hash_of_mixed_weighted SmartSpanningTrees(graph_hash_of_mixed_weighted& input_graph) {

	/*input_graph may be disconnected; SmartSpanningTrees are forests; time complexity: O(|E|+|V|log|V|)*/

	/*a new graph with smart edge costs; time complexity: O(E)*/
	graph_hash_of_mixed_weighted new_graph = graph_hash_of_mixed_weighted_copy_graph(input_graph);
	for (auto it = new_graph.hash_of_vectors.begin(); it != new_graph.hash_of_vectors.end(); it++) {
		int v = it->first;
		double nw_v = it->second.vertex_weight;
		auto search = new_graph.hash_of_hashs.find(v);
		if (search != new_graph.hash_of_hashs.end()) {
			for (auto it2 = search->second.begin(); it2 != search->second.end(); it2++) {
				int vertex = it2->first;
				if (v < vertex) {
					double nw_vertex = new_graph.hash_of_vectors[vertex].vertex_weight;
					double new_ec = 2;
					if (nw_v > 0) { // nodes with positive weights are queried
						new_ec--;
					}
					if (nw_vertex > 0) {
						new_ec--;
					}
					graph_hash_of_mixed_weighted_add_edge(new_graph, v, vertex, new_ec);// change edge weights
				}
			}
		}
		else {
			auto search2 = new_graph.hash_of_vectors.find(v);
			for (auto it2 = search2->second.adj_vertices.begin(); it2 != search2->second.adj_vertices.end(); it2++) {
				int vertex = it2->first;
				if (v < vertex) {
					double nw_vertex = new_graph.hash_of_vectors[vertex].vertex_weight;
					double new_ec = 2;
					if (nw_v > 0) { // nodes with positive weights are queried
						new_ec--;
					}
					if (nw_vertex > 0) {
						new_ec--;
					}
					graph_hash_of_mixed_weighted_add_edge(new_graph, v, vertex, new_ec);// change edge weights
				}
			}
		}
	}

	/*add dummy vertices and edges for disconnected input_graph; time complexity: O(V)*/
	for (auto it = new_graph.hash_of_vectors.begin(); it != new_graph.hash_of_vectors.end(); it++) {
		int v = it->first;
		graph_hash_of_mixed_weighted_add_edge(new_graph, v, INT_MAX, INT_MAX);
	}

	/*find MST; time complexity: O(|E|+|V|log|V|)*/
	std::unordered_map<int, int> predessors = graph_hash_of_mixed_weighted_minimum_spanning_tree(new_graph);

	/*build SmartSpanningTrees; no memory leak below*/
	graph_hash_of_mixed_weighted SmartSpanningTrees;
	for (auto it = input_graph.hash_of_vectors.begin(); it != input_graph.hash_of_vectors.end(); it++) {
		int v = it->first;
		double nw_v = it->second.vertex_weight;
		graph_hash_of_mixed_weighted_add_vertex(SmartSpanningTrees, v, nw_v); // add all vertices
	}
	for (auto it = predessors.begin(); it != predessors.end(); ++it) {
		if (it->first != it->second && it->first != INT_MAX && it->second != INT_MAX) { // non-dummy edges in SmartSpanningTree
			double ec = graph_hash_of_mixed_weighted_edge_weight(input_graph, it->first, it->second);
			graph_hash_of_mixed_weighted_add_edge(SmartSpanningTrees, it->first, it->second, ec);
		}
	}

	return SmartSpanningTrees;

}
#pragma endregion SmartSpanningTrees

#pragma region
pair<graph_hash_of_mixed_weighted, pair<int, int>> Smart_ST(pair<int, int> input_time_interval, graph_hash_of_mixed_weighted& input_graph,
	graph_hash_of_mixed_weighted& query_state_graph, double alpha) {

	std::list<std::list<int>> cpns = graph_hash_of_mixed_weighted_connected_components(input_graph);

	vector<pair<pair<int, int>, int>> Phi = sorted_all_time_subintervals(input_time_interval);

	pair<graph_hash_of_mixed_weighted, pair<int, int>> Theta_best; // <tree, time_subinterval>
	double w_Theta_best = -INT_MAX;

	graph_hash_of_mixed_weighted static_bump_best;
	double w_static_bump_best = -INT_MAX;

	update_nw_ec_most_generous_way(input_time_interval, query_state_graph, input_graph, alpha); // in input_graph, queried vertices have positive weights, while not-queried vertices have 0 weight


	for (auto it0 = cpns.begin(); it0 != cpns.end(); it0++) {

		graph_hash_of_mixed_weighted cpn_graph = graph_hash_of_mixed_weighted_extract_subgraph_for_a_list_of_vertices(input_graph, *it0);

		graph_hash_of_mixed_weighted smart_tree = SmartSpanningTrees(cpn_graph);

		graph_hash_of_mixed_weighted Theta_T_i2 = graph_hash_of_mixed_weighted_General_Pruning_tree(smart_tree);

		double w_Theta_T_i2 = PCST_weight(Theta_T_i2);

		if (w_Theta_T_i2 > w_static_bump_best) {
			w_static_bump_best = w_Theta_T_i2;
			static_bump_best = Theta_T_i2;
		}

	}


	/*find best pair of subtree of time subinterval*/
	for (int xx = 0; xx < Phi.size(); xx++) {
		pair<int, int> T_i = Phi[xx].first;

		build_G_dash_T_i(static_bump_best, query_state_graph, T_i, alpha);

		static_bump_best = graph_hash_of_mixed_weighted_General_Pruning_tree(static_bump_best);

		if (static_bump_best.hash_of_vectors.size() > 0) {
			double L_for_upper_bound;
			std::unordered_set<string> Omega3;
			update_solution(Theta_best, static_bump_best, L_for_upper_bound, w_Theta_best, T_i, Omega3);
		}
	}



	return Theta_best;

}
#pragma endregion Smart_ST

#pragma region
pair<graph_hash_of_mixed_weighted, pair<int, int>> PCST(pair<int, int> input_time_interval, graph_hash_of_mixed_weighted& input_graph, graph_hash_of_mixed_weighted& query_state_graph, double alpha) {

	std::list<std::list<int>> cpns = graph_hash_of_mixed_weighted_connected_components(input_graph);

	vector<pair<pair<int, int>, int>> Phi = sorted_all_time_subintervals(input_time_interval);

	pair<graph_hash_of_mixed_weighted, pair<int, int>> Theta_best; // <tree, time_subinterval>
	double w_Theta_best = -INT_MAX;

	graph_hash_of_mixed_weighted static_bump_best;
	double w_static_bump_best = -INT_MAX;

	update_nw_ec_most_generous_way(input_time_interval, query_state_graph, input_graph, alpha); // in input_graph, queried vertices have positive weights, while not-queried vertices have 0 weight

	for (auto it0 = cpns.begin(); it0 != cpns.end(); it0++) {

		graph_hash_of_mixed_weighted cpn_graph = graph_hash_of_mixed_weighted_extract_subgraph_for_a_list_of_vertices(input_graph, *it0);

		graph_hash_of_mixed_weighted smart_tree = graph_hash_of_mixed_weighted_Fast_GW_Growing_tree(cpn_graph, "tree");

		graph_hash_of_mixed_weighted Theta_T_i2 = graph_hash_of_mixed_weighted_General_Pruning_tree(smart_tree);

		double w_Theta_T_i2 = PCST_weight(Theta_T_i2);

		if (w_Theta_T_i2 > w_static_bump_best) {
			w_static_bump_best = w_Theta_T_i2;
			static_bump_best = Theta_T_i2;
		}

	}

	/*find best pair of subtree of time subinterval*/
	for (int xx = 0; xx < Phi.size(); xx++) {
		pair<int, int> T_i = Phi[xx].first;

		build_G_dash_T_i(static_bump_best, query_state_graph, T_i, alpha);

		static_bump_best = graph_hash_of_mixed_weighted_General_Pruning_tree(static_bump_best);

		if (static_bump_best.hash_of_vectors.size() > 0) {
			double L_for_upper_bound;
			std::unordered_set<string> Omega3;
			update_solution(Theta_best, static_bump_best, L_for_upper_bound, w_Theta_best, T_i, Omega3);
		}
	}



	return Theta_best;

}
#pragma endregion PCST



/*Experiments*/

#pragma region 
void read_road_data(graph_hash_of_mixed_weighted& read_graph, string city_name,
	std::unordered_map<int, pair<double, double>>& read_intersection_lon_and_lat) {

	/*this function can clear existing graph data; time complexity: O(V+E)*/
	read_graph.clear();
	read_intersection_lon_and_lat.clear();

	string file_name = city_name + "//" + city_name + "_road_network_intersections.txt"; // the txt file is in the folder "NY"

	string line_content;
	ifstream myfile(file_name); // open the file
	if (myfile.is_open()) // if the file is opened successfully
	{
		while (getline(myfile, line_content)) // read file line by line
		{
			std::vector<string> Parsed_content = parse_string(line_content, " "); // parse line_content
			int INTERSECTION_ID = stoi(Parsed_content[1]);
			double lon = stod(Parsed_content[2]);
			double lat = stod(Parsed_content[3]);
			read_intersection_lon_and_lat[INTERSECTION_ID] = { lon , lat };
			graph_hash_of_mixed_weighted_add_vertex(read_graph, INTERSECTION_ID, 0); // initial vertex weight is 0 
		}
		myfile.close(); //close the file
	}
	else
	{
		std::cout << "Unable to open file " << file_name << endl << "Please check the file location or file name." << endl; // throw an error message
		getchar(); // keep the console window
		exit(1); // end the program
	}



	file_name = city_name + "//" + city_name + "_road_network_roads.txt";
	ifstream myfile2(file_name); // open the file
	if (myfile2.is_open()) // if the file is opened successfully
	{
		while (getline(myfile2, line_content)) // read file line by line
		{
			std::vector<string> Parsed_content = parse_string(line_content, " "); // parse line_content
			int id1 = stoi(Parsed_content[1]);
			int id2 = stoi(Parsed_content[2]);
			graph_hash_of_mixed_weighted_add_edge(read_graph, id1, id2, 0); // initial edge weight is 0 
		}
		myfile2.close(); //close the file
	}
	else
	{
		std::cout << "Unable to open file " << file_name << endl << "Please check the file location or file name." << endl; // throw an error message
		getchar(); // keep the console window
		exit(1); // end the program
	}

	cout << "graph_hash_of_mixed_weighted_num_vertices(read_graph): "
		<< graph_hash_of_mixed_weighted_num_vertices(read_graph) << endl;
	cout << "graph_hash_of_mixed_weighted_num_edges(read_graph): "
		<< graph_hash_of_mixed_weighted_num_edges(read_graph) << endl;



}
#pragma endregion read_road_data 

#pragma region 
void read_taxi_data_in_a_day_precision_hour(graph_hash_of_mixed_weighted& taxi_data_graph, string city_name,
	int day, bool count_pickup, bool count_dropoff) {

	/*this function can clear existing graph data;
	the number of activities at intersection j in hour i is the edge weight of (i,j) in taxi_data_graph;
	both pickup and dropoff activities are counted when count_pickup = count_dropoff = true;

	time complexity: O(number of taxi trips)*/

	string file_name = "NY//NY_taxi_trip_2015_1_" + to_string(day) + ".txt"; // the txt file is in the folder "NY"

	string line_content;
	ifstream myfile(file_name); // open the file
	if (myfile.is_open()) // if the file is opened successfully
	{
		while (getline(myfile, line_content)) // read file line by line
		{
			/*start_year,start_month,start_day,start_hour,start_minute,
			 start_intersection,end_year,end_month,end_day,end_hour,end_minute,end_intersection*/
			std::vector<string> Parsed_content = parse_string(line_content, ","); // parse line_content
			int start_day = stoi(Parsed_content[2]);
			int start_hour = stoi(Parsed_content[3]); // 0 .. 23
			int start_intersection = stoi(Parsed_content[5]);
			int end_day = stoi(Parsed_content[8]);
			int end_hour = stoi(Parsed_content[9]);
			int end_intersection = stoi(Parsed_content[11]);

			if (start_day == day && count_pickup == true) {
				graph_hash_of_mixed_weighted_edge_weight_plus_value
				(taxi_data_graph, time_ID_start + 24 * (day - 1) + start_hour, start_intersection, 1);
			}
			if (end_day == day && count_dropoff == true) {
				graph_hash_of_mixed_weighted_edge_weight_plus_value
				(taxi_data_graph, time_ID_start + 24 * (day - 1) + end_hour, end_intersection, 1);
			}
		}
		myfile.close(); //close the file
	}
	else
	{
		std::cout << "Unable to open file " << file_name << endl << "Please check the file location or file name." << endl; // throw an error message
		getchar(); // keep the console window
		exit(1); // end the program
	}

	//graph_hash_of_mixed_weighted_print(taxi_data_graph);

}
#pragma endregion read_taxi_data_in_a_day_precision_hour

#pragma region 
void read_Wiki_graph_data(graph_hash_of_mixed_weighted& read_graph, std::unordered_map<int, string>& page_names) {

	/*this function can clear existing graph data*/
	read_graph.clear();
	page_names.clear();

	string file_name = "Wiki_1M//Wiki_pages_1176k_undirected.txt";
	string line_content;
	ifstream myfile(file_name); // open the file
	if (myfile.is_open()) // if the file is opened successfully
	{
		while (getline(myfile, line_content)) // read file line by line
		{
			//cout << line_content << endl;
			std::vector<string> Parsed_content = parse_string(line_content, " "); // parse line_content
			int id = stoi(Parsed_content[0]);
			string name = Parsed_content[1];
			page_names[id] = name;
			graph_hash_of_mixed_weighted_add_vertex(read_graph, id, 0); // initial vertex weight is 0 
		}
		myfile.close(); //close the file
	}
	else
	{
		std::cout << "Unable to open file " << file_name << endl << "Please check the file location or file name." << endl; // throw an error message
		getchar(); // keep the console window
		exit(1); // end the program
	}

	file_name = "Wiki_1M//Wiki_pagerelationships_1176k_undirected.txt";
	ifstream myfile2(file_name); // open the file
	if (myfile2.is_open()) // if the file is opened successfully
	{
		while (getline(myfile2, line_content)) // read file line by line
		{
			std::vector<string> Parsed_content = parse_string(line_content, " "); // parse line_content
			int id1 = stoi(Parsed_content[0]);
			int id2 = stoi(Parsed_content[1]);
			graph_hash_of_mixed_weighted_add_edge(read_graph, id1, id2, 0); // initial edge weight is 0 
		}
		myfile2.close(); //close the file
	}
	else
	{
		std::cout << "Unable to open file " << file_name << endl << "Please check the file location or file name." << endl; // throw an error message
		getchar(); // keep the console window
		exit(1); // end the program
	}

	cout << "graph_hash_of_mixed_weighted_num_vertices(read_graph): "
		<< graph_hash_of_mixed_weighted_num_vertices(read_graph) << endl;
	cout << "graph_hash_of_mixed_weighted_num_edges(read_graph): "
		<< graph_hash_of_mixed_weighted_num_edges(read_graph) << endl;



}
#pragma endregion read_Wiki_graph_data 

#pragma region 
double letter_to_hour(const std::string& c) {

	if (c == "A")
	{
		return 0;
	}
	else if (c == "B")
	{
		return 1;
	}
	else if (c == "C")
	{
		return 2;
	}
	else if (c == "D")
	{
		return 3;
	}
	else if (c == "E")
	{
		return 4;
	}
	else if (c == "F")
	{
		return 5;
	}
	else if (c == "G")
	{
		return 6;
	}
	else if (c == "H")
	{
		return 7;
	}
	else if (c == "I")
	{
		return 8;
	}
	else if (c == "J")
	{
		return 9;
	}
	else if (c == "K")
	{
		return 10;
	}
	else if (c == "L")
	{
		return 11;
	}
	else if (c == "M")
	{
		return 12;
	}
	else if (c == "N")
	{
		return 13;
	}
	else if (c == "O")
	{
		return 14;
	}
	else if (c == "P")
	{
		return 15;
	}
	else if (c == "Q")
	{
		return 16;
	}
	else if (c == "R")
	{
		return 17;
	}
	else if (c == "S")
	{
		return 18;
	}
	else if (c == "T")
	{
		return 19;
	}
	else if (c == "U")
	{
		return 20;
	}
	else if (c == "V")
	{
		return 21;
	}
	else if (c == "W")
	{
		return 22;
	}
	else if (c == "X")
	{
		return 23;
	}

}

void read_Wiki_pageview_data_in_a_day_precision_hour(graph_hash_of_mixed_weighted& Wiki_pageview_graph, int day) {

	/*this function can clear existing graph data;

	the number of activities at page j in hour i is the edge weight of (i,j) in Wiki_pageview_graph;

	time complexity: O(24 * number of pages)*/

	string file_name = "Wiki_1M//pageviews_1176k_2020_1_" + to_string(day) + ".txt"; // the txt file is in the folder "Wiki"
	string line_content;
	ifstream myfile(file_name); // open the file
	if (myfile.is_open()) // if the file is opened successfully
	{
		while (getline(myfile, line_content)) // read file line by line
		{
			//cout << line_content << endl;

			/*57915 1 J1*/
			std::vector<string> Parsed_content = parse_string(line_content, " "); // parse line_content
			int page_id = stoi(Parsed_content[0]);

			int hour_id;
			int count_num;
			bool pair_data_stored = false;
			string num_s; // may be more than one char
			for (auto it = Parsed_content[2].begin(); it != Parsed_content[2].end(); it++) {
				/*string class has a constructor that allows us to specify size of
					string as first parameter and character to be filled in given size as second parameter.*/
				string s(1, *it);
				if (string_is_number(s) == false) { // *it is hour letter
					hour_id = letter_to_hour(s);
				}
				else { // *it is a part of count number
					num_s.push_back(*it);
					it++;
					string x(1, *it);
					if (it == Parsed_content[2].end() || string_is_number(x) == false) { // a number is complete
						count_num = stoi(num_s);
						num_s.clear();
						graph_hash_of_mixed_weighted_add_edge
						(Wiki_pageview_graph, time_ID_start + 24 * (day - 1) + hour_id, page_id, count_num);
					}
					it--;
				}
			}
		}
		myfile.close(); //close the file
	}
	else
	{
		std::cout << "Unable to open file " << file_name << endl << "Please check the file location or file name." << endl; // throw an error message
		getchar(); // keep the console window
		exit(1); // end the program
	}

	//graph_hash_of_mixed_weighted_print(Wiki_pageview_graph);

}
#pragma endregion read_Wiki_pageview_data_in_a_day_precision_hour

#pragma region 
void read_Reddit_Keywords(graph_hash_of_mixed_weighted& read_graph) {

	string file_name = "Reddit//Keywords.txt";
	string line_content;
	ifstream myfile(file_name); // open the file
	if (myfile.is_open()) // if the file is opened successfully
	{
		int xx = 0;
		while (getline(myfile, line_content)) // read file line by line
		{
			xx++;
			if (xx > 1) {
				std::vector<string> Parsed_content = parse_string(line_content, "	"); // parse line_content
				int id = stoi(Parsed_content[1]);
				graph_hash_of_mixed_weighted_add_vertex(read_graph, id, 0); // initial vertex weight is 0
			}
		}
		myfile.close(); //close the file
	}
	else
	{
		std::cout << "Unable to open file " << file_name << endl << "Please check the file location or file name." << endl; // throw an error message
		getchar(); // keep the console window
		exit(1); // end the program
	}

}

void read_Reddit_Communities(graph_hash_of_mixed_weighted& read_graph) {

	string file_name = "Reddit//Communities.txt";
	string line_content;
	ifstream myfile(file_name); // open the file
	if (myfile.is_open()) // if the file is opened successfully
	{
		int xx = 0;
		while (getline(myfile, line_content)) // read file line by line
		{
			xx++;
			if (xx > 1) {
				std::vector<string> Parsed_content = parse_string(line_content, "	"); // parse line_content
				int id = stoi(Parsed_content[1]);
				graph_hash_of_mixed_weighted_add_vertex(read_graph, id, 0); // initial vertex weight is 0
			}
		}
		myfile.close(); //close the file
	}
	else
	{
		std::cout << "Unable to open file " << file_name << endl << "Please check the file location or file name." << endl; // throw an error message
		getchar(); // keep the console window
		exit(1); // end the program
	}

}

void read_Reddit_vertex_IDs_and_edges(graph_hash_of_mixed_weighted& read_graph) {

	string file_name = "Reddit//dummy_vertex_IDs.txt";
	string line_content;
	ifstream myfile(file_name); // open the file
	if (myfile.is_open()) // if the file is opened successfully
	{
		int xx = 0;
		while (getline(myfile, line_content)) // read file line by line
		{
			xx++;
			if (xx > 1) {
				std::vector<string> Parsed_content = parse_string(line_content, "	"); // parse line_content
				int dummy_id = stoi(Parsed_content[1]);
				std::vector<string> Parsed_content2 = parse_string(Parsed_content[0], "+");
				int Community_ID = stoi(Parsed_content2[0]);
				int Keyword_ID = stoi(Parsed_content2[1]);
				graph_hash_of_mixed_weighted_add_edge(read_graph, dummy_id, Community_ID, 0); // initial edge weight is 0
				graph_hash_of_mixed_weighted_add_edge(read_graph, dummy_id, Keyword_ID, 0);
			}
		}
		myfile.close(); //close the file
	}
	else
	{
		std::cout << "Unable to open file " << file_name << endl << "Please check the file location or file name." << endl; // throw an error message
		getchar(); // keep the console window
		exit(1); // end the program
	}

}

void read_Reddit_graph_data(graph_hash_of_mixed_weighted& read_graph) {

	/*this function can clear existing graph data;
	time complexity: O(V+E)*/
	read_graph.clear();

	read_Reddit_Keywords(read_graph);
	read_Reddit_Communities(read_graph);
	read_Reddit_vertex_IDs_and_edges(read_graph);

	cout << "graph_hash_of_mixed_weighted_num_vertices(read_graph): "
		<< graph_hash_of_mixed_weighted_num_vertices(read_graph) << endl;
	cout << "graph_hash_of_mixed_weighted_num_edges(read_graph): "
		<< graph_hash_of_mixed_weighted_num_edges(read_graph) << endl;

}
#pragma endregion read_Reddit_graph_data 

#pragma region 
void read_Reddit_comment_data_in_a_day_precision_hour(graph_hash_of_mixed_weighted& full_query_state_graph, int day) {

	/*time complexity: O(24 * number of pages)*/

	string file_name = "Reddit//Comments_2019_9_" + to_string(day) + ".txt";
	string line_content;
	ifstream myfile(file_name); // open the file
	if (myfile.is_open()) // if the file is opened successfully
	{
		int xxx = 0;
		while (getline(myfile, line_content)) // read file line by line
		{
			xxx++;

			if (xxx > 1) {
				/*2604152	6_2,7_5*/
				std::vector<string> Parsed_content = parse_string(line_content, "	"); // parse line_content
				int dummy_id = stoi(Parsed_content[0]);

				std::vector<string> unparsed_comments = parse_string(Parsed_content[1], ",");
				for (int x = unparsed_comments.size() - 1; x >= 0; x--) {
					std::vector<string> comment_time_num = parse_string(unparsed_comments[x], "_");
					int hour = stoi(comment_time_num[0]);
					int count_num = stoi(comment_time_num[1]);
					graph_hash_of_mixed_weighted_add_edge(full_query_state_graph, time_ID_start + 24 * (day - 1) + hour, dummy_id, count_num);
				}
			}

		}
		myfile.close(); //close the file
	}
	else
	{
		std::cout << "Unable to open file " << file_name << endl << "Please check the file location or file name." << endl; // throw an error message
		getchar(); // keep the console window
		exit(1); // end the program
	}

}
#pragma endregion read_Reddit_comment_data_in_a_day_precision_hour

#pragma region 
graph_hash_of_mixed_weighted produce_small_query_state_graph_intensive(graph_hash_of_mixed_weighted& full_query_state_graph,
	graph_hash_of_mixed_weighted& small_input_graph, double top_p, int start_time_ID, int end_time_ID) {

	/* V is the number of vertices

	for NY taxi, taxi_data_graph is query_state_graph;
	for Wiki, Wiki_pageview_graph is query_state_graph;

	this function turns query_state_graph with activity counts into new query_state_graph,
	where a vertex is linked to a time slot only when this vertex is queried in this time slot;

	a vertex is queried in a time slot if the activity counts of this vertex is within top top_p % of all
	vertices in this time slot;

	time complexity: O((end_time_ID - start_time_ID) * E log E)*/

	graph_hash_of_mixed_weighted small_query_state_graph;
	for (auto it = small_input_graph.hash_of_vectors.begin(); it != small_input_graph.hash_of_vectors.end(); it++) {
		graph_hash_of_mixed_weighted_add_vertex(small_query_state_graph, it->first, 0); // guarantee that small_query_state_graph contains all vertices in small_input_graph
	}

	for (int id = start_time_ID; id <= end_time_ID; id++) {
		int time_ID = id;

		/*get the top_p threshold query value for this time slot; time complexity: O(E log E)*/
		vector<double> count_numbers_in_time_ID;
		auto search = full_query_state_graph.hash_of_hashs.find(time_ID);
		if (search != full_query_state_graph.hash_of_hashs.end()) { // time_ID is in hash_of_hashs
			for (auto it = search->second.begin(); it != search->second.end(); ++it) {
				if (small_input_graph.hash_of_vectors.count(it->first) > 0) {
					count_numbers_in_time_ID.push_back(it->second); // a count number in time_ID
				}
			}
		}
		else {
			auto search2 = full_query_state_graph.hash_of_vectors.find(time_ID);
			if (search2 != full_query_state_graph.hash_of_vectors.end()) { // time_ID is in input_graph, otherwise return empty list
				for (auto it = search2->second.adj_vertices.begin(); it != search2->second.adj_vertices.end(); ++it) {
					if (small_input_graph.hash_of_vectors.count(it->first) > 0) {
						count_numbers_in_time_ID.push_back(it->second); // a count number in time_ID
					}
				}
			}
		}
		int zero_count_vertex_num = small_input_graph.hash_of_vectors.size() - count_numbers_in_time_ID.size();
		for (int xx = 0; xx < zero_count_vertex_num; xx++) {
			count_numbers_in_time_ID.push_back(0); // vertices not in query_state_graph; they have no acticity in this time slot
		}
		double threshold = top_percent_threshold_change_vector(count_numbers_in_time_ID, top_p);

		graph_hash_of_mixed_weighted_add_vertex(small_query_state_graph, time_ID, 0); // guarantee that small_query_state_graph contains all time_IDs

		/*a vertex is queried in a time slot if the activity counts of this vertex >= threshold & >0 in this time slot*/
		if (search != full_query_state_graph.hash_of_hashs.end()) { // time_ID is in hash_of_hashs
			for (auto it = search->second.begin(); it != search->second.end(); ++it) {
				if (it->second >= threshold && it->second > 0 && small_input_graph.hash_of_vectors.count(it->first) > 0) {
					graph_hash_of_mixed_weighted_add_edge(small_query_state_graph, time_ID, it->first, 1); // vertex it->first is queried in this time slot
				}
			}
		}
		else {
			auto search2 = full_query_state_graph.hash_of_vectors.find(time_ID);
			if (search2 != full_query_state_graph.hash_of_vectors.end()) { // time_ID is in input_graph, otherwise return empty list
				for (auto it = search2->second.adj_vertices.begin(); it != search2->second.adj_vertices.end(); ++it) {
					if (it->second >= threshold && it->second > 0 && small_input_graph.hash_of_vectors.count(it->first) > 0) {
						graph_hash_of_mixed_weighted_add_edge(small_query_state_graph, time_ID, it->first, 1); // vertex it->first is queried in this time slot
					}
				}
			}
		}

	}

	return small_query_state_graph;

}
#pragma endregion produce_small_query_state_graph_intensive

#pragma region 
graph_hash_of_mixed_weighted produce_small_query_state_graph_abnormal(graph_hash_of_mixed_weighted& full_query_state_graph,
	graph_hash_of_mixed_weighted& small_input_graph, double q_percent, int start_time_ID, int end_time_ID) {

	/*
	this function turns query_state_graph with activity counts into new query_state_graph,
	where a vertex is linked to a time slot only when this vertex is queried in this time slot;

	a vertex is queried in a time slot if the activity counts of this vertex increases more than q_percent % from the last day */

	graph_hash_of_mixed_weighted small_query_state_graph;
	for (auto it = small_input_graph.hash_of_vectors.begin(); it != small_input_graph.hash_of_vectors.end(); it++) {
		graph_hash_of_mixed_weighted_add_vertex(small_query_state_graph, it->first, 0); // guarantee that small_query_state_graph contains all vertices in small_input_graph
	}

	for (int id = start_time_ID; id <= end_time_ID; id++) {
		int time_ID = id;

		graph_hash_of_mixed_weighted_add_vertex(small_query_state_graph, time_ID, 0); // guarantee that small_query_state_graph contains all time_IDs

		for (auto it = small_input_graph.hash_of_vectors.begin(); it != small_input_graph.hash_of_vectors.end(); it++) {
			int vertex = it->first;

			double vertex_activity_count_time_ID = 0;
			if (graph_hash_of_mixed_weighted_contain_edge(full_query_state_graph, vertex, time_ID)) {
				vertex_activity_count_time_ID = graph_hash_of_mixed_weighted_edge_weight(full_query_state_graph, vertex, time_ID);
			}

			double vertex_activity_count_last_day = 0;
			if (graph_hash_of_mixed_weighted_contain_edge(full_query_state_graph, vertex, time_ID - 24)) {
				vertex_activity_count_last_day = graph_hash_of_mixed_weighted_edge_weight(full_query_state_graph, vertex, time_ID - 24);
			}

			/**/
			if (vertex_activity_count_last_day > 0 &&
				vertex_activity_count_time_ID > vertex_activity_count_last_day* (1 + q_percent / 100)) { // this is abnormal
				graph_hash_of_mixed_weighted_add_edge(small_query_state_graph, time_ID, vertex, 1); // vertex is queried in this time slot
			}

		}

	}

	return small_query_state_graph;

}
#pragma endregion produce_small_query_state_graph_abnormal

#pragma region
double produce_S_MIRROR_UB(pair<int, int> input_time_interval, graph_hash_of_mixed_weighted& instance_graph,
	graph_hash_of_mixed_weighted& query_state_graph, double alpha, int reduced_V, double weight_S_MIRROR, double kappa_1, double kappa_2) {

	int V_pos = 0;
	for (auto it = instance_graph.hash_of_vectors.begin(); it != instance_graph.hash_of_vectors.end(); it++) {
		int v = it->first;
		bool queried_once = false;
		for (int i = input_time_interval.first; i <= input_time_interval.second; i++) {
			if (graph_hash_of_mixed_weighted_contain_edge(query_state_graph, i, v)) {
				queried_once = true;
				break;
			}
		}
		if (queried_once == true) {
			V_pos++;
		}
	}

	double S_MIRROR_UB = reduced_V;
	double x = (1 + alpha) * (double)V_pos - alpha / ((double)input_time_interval.second - input_time_interval.first + 1);
	if (S_MIRROR_UB > x) {
		S_MIRROR_UB = x;
	}

	if (kappa_1 > kappa_2) {
		return S_MIRROR_UB + 2 * weight_S_MIRROR + kappa_1;
	}
	else {
		return S_MIRROR_UB + 2 * weight_S_MIRROR + kappa_2;
	}

}
#pragma endregion produce_S_MIRROR_UB

#pragma region
void load_algorithms(pair<int, int> input_time_interval, graph_hash_of_mixed_weighted& instance_graph,
	graph_hash_of_mixed_weighted& query_state_graph, double alpha, int h, int depth, int s,
	double& time_MIRROR, double& weight_MIRROR, double& time_S_MIRROR, double& weight_S_MIRROR,
	double& time_H_MIRROR, double& weight_H_MIRROR, double& time_H_S_MIRROR, double& weight_H_S_MIRROR,
	double& time_MIRROR_Basic, double& weight_MIRROR_Basic, double& time_S_MIRROR_Basic, double& weight_S_MIRROR_Basic,
	double& time_Smart_ST, double& weight_Smart_ST, double& time_Random_ST, double& weight_Random_ST,
	double& time_BF_ST, double& weight_BF_ST, double& time_PCST, double& weight_PCST,
	double& MIRROR_for_upper_bound, double& kappa_1, double& kappa_2, int& reduced_V, double& MIRROR_Basic_for_upper_bound, double& S_MIRROR_Basic_for_upper_bound,
	bool use_MIRROR, bool use_S_MIRROR, bool use_H_MIRROR, bool use_H_S_MIRROR, bool use_MIRROR_Basic, bool use_S_MIRROR_Basic,
	bool use_Smart_ST, bool use_Random_ST, bool use_BF_ST, bool use_PCST,
	double& time_MIRROR_onlyreduction, double& weight_MIRROR_onlyreduction, double& time_S_MIRROR_onlyreduction, double& weight_S_MIRROR_onlyreduction,
	double& time_MIRROR_onlyBandB, double& weight_MIRROR_onlyBandB, double& time_S_MIRROR_onlyBandB, double& weight_S_MIRROR_onlyBandB,
	bool use_MIRROR_onlyreduction, bool use_S_MIRROR_onlyreduction, bool use_MIRROR_onlyBandB, bool use_S_MIRROR_onlyBandB) {

	if (use_MIRROR == true) {
		auto begin1 = std::chrono::high_resolution_clock::now();
		pair<graph_hash_of_mixed_weighted, pair<int, int>> solu_MIRROR = accelerated_MIRROR
		({ input_time_interval.first, input_time_interval.second }, instance_graph, query_state_graph, alpha, MIRROR_for_upper_bound, 1, 1);
		auto end1 = std::chrono::high_resolution_clock::now();
		time_MIRROR = std::chrono::duration_cast<std::chrono::nanoseconds>(end1 - begin1).count() / 1e9; // s
		weight_MIRROR = net_weight_PCSTPTG_single_bump(solu_MIRROR.first, solu_MIRROR.second, query_state_graph, alpha);
	}
	else {
		time_MIRROR = 0;
		weight_MIRROR = 0;
	}

	if (use_S_MIRROR == true) {
		auto begin2 = std::chrono::high_resolution_clock::now();
		pair<graph_hash_of_mixed_weighted, pair<int, int>> solu_S_MIRROR = accelerated_S_MIRROR
		({ input_time_interval.first, input_time_interval.second }, instance_graph, query_state_graph, alpha, kappa_1, reduced_V, h, kappa_2, 1, 1);
		auto end2 = std::chrono::high_resolution_clock::now();
		time_S_MIRROR = std::chrono::duration_cast<std::chrono::nanoseconds>(end2 - begin2).count() / 1e9; // s
		weight_S_MIRROR = net_weight_PCSTPTG_single_bump(solu_S_MIRROR.first, solu_S_MIRROR.second, query_state_graph, alpha);
	}
	else {
		time_S_MIRROR = 0;
		weight_S_MIRROR = 0;
	}

	if (use_H_MIRROR == true) {
		auto begin1 = std::chrono::high_resolution_clock::now();
		pair<graph_hash_of_mixed_weighted, pair<int, int>> solu_MIRROR = accelerated_H_MIRROR
		({ input_time_interval.first, input_time_interval.second }, instance_graph, query_state_graph, alpha, depth);
		auto end1 = std::chrono::high_resolution_clock::now();
		time_H_MIRROR = std::chrono::duration_cast<std::chrono::nanoseconds>(end1 - begin1).count() / 1e9; // s
		weight_H_MIRROR = net_weight_PCSTPTG_single_bump(solu_MIRROR.first, solu_MIRROR.second, query_state_graph, alpha);
	}
	else {
		time_H_MIRROR = 0;
		weight_H_MIRROR = 0;
	}

	if (use_H_S_MIRROR == true) {
		auto begin2 = std::chrono::high_resolution_clock::now();
		pair<graph_hash_of_mixed_weighted, pair<int, int>> solu_S_MIRROR = accelerated_H_S_MIRROR
		({ input_time_interval.first, input_time_interval.second }, instance_graph, query_state_graph, alpha, h, depth);
		auto end2 = std::chrono::high_resolution_clock::now();
		time_H_S_MIRROR = std::chrono::duration_cast<std::chrono::nanoseconds>(end2 - begin2).count() / 1e9; // s
		weight_H_S_MIRROR = net_weight_PCSTPTG_single_bump(solu_S_MIRROR.first, solu_S_MIRROR.second, query_state_graph, alpha);
	}
	else {
		time_H_S_MIRROR = 0;
		weight_H_S_MIRROR = 0;
	}

	if (use_MIRROR_Basic == true) {
		auto begin1 = std::chrono::high_resolution_clock::now();
		double x;
		pair<graph_hash_of_mixed_weighted, pair<int, int>> solu_MIRROR = accelerated_MIRROR
		({ input_time_interval.first, input_time_interval.second }, instance_graph, query_state_graph, alpha, x, 0, 0);
		auto end1 = std::chrono::high_resolution_clock::now();
		time_MIRROR_Basic = std::chrono::duration_cast<std::chrono::nanoseconds>(end1 - begin1).count() / 1e9; // s
		weight_MIRROR_Basic = net_weight_PCSTPTG_single_bump(solu_MIRROR.first, solu_MIRROR.second, query_state_graph, alpha);
	}
	else {
		time_MIRROR_Basic = 0;
		weight_MIRROR_Basic = 0;
	}

	if (use_S_MIRROR_Basic == true) {
		auto begin2 = std::chrono::high_resolution_clock::now();
		double x, y;
		int w;
		pair<graph_hash_of_mixed_weighted, pair<int, int>> solu_S_MIRROR = accelerated_S_MIRROR
		({ input_time_interval.first, input_time_interval.second }, instance_graph, query_state_graph, alpha, x, w, h, y, 0, 0);
		auto end2 = std::chrono::high_resolution_clock::now();
		time_S_MIRROR_Basic = std::chrono::duration_cast<std::chrono::nanoseconds>(end2 - begin2).count() / 1e9; // s
		weight_S_MIRROR_Basic = net_weight_PCSTPTG_single_bump(solu_S_MIRROR.first, solu_S_MIRROR.second, query_state_graph, alpha);
	}
	else {
		time_S_MIRROR_Basic = 0;
		weight_S_MIRROR_Basic = 0;
	}

	if (use_MIRROR_onlyreduction == true) {
		auto begin1 = std::chrono::high_resolution_clock::now();
		double x;
		pair<graph_hash_of_mixed_weighted, pair<int, int>> solu_MIRROR = accelerated_MIRROR
		({ input_time_interval.first, input_time_interval.second }, instance_graph, query_state_graph, alpha, x, 1, 0);
		auto end1 = std::chrono::high_resolution_clock::now();
		time_MIRROR_onlyreduction = std::chrono::duration_cast<std::chrono::nanoseconds>(end1 - begin1).count() / 1e9; // s
		weight_MIRROR_onlyreduction = net_weight_PCSTPTG_single_bump(solu_MIRROR.first, solu_MIRROR.second, query_state_graph, alpha);
	}
	else {
		time_MIRROR_onlyreduction = 0;
		weight_MIRROR_onlyreduction = 0;
	}

	if (use_S_MIRROR_onlyreduction == true) {
		auto begin1 = std::chrono::high_resolution_clock::now();
		double x, y;
		int w;
		pair<graph_hash_of_mixed_weighted, pair<int, int>> solu_MIRROR = accelerated_S_MIRROR
		({ input_time_interval.first, input_time_interval.second }, instance_graph, query_state_graph, alpha, x, w, h, y, 1, 0);
		auto end1 = std::chrono::high_resolution_clock::now();
		time_S_MIRROR_onlyreduction = std::chrono::duration_cast<std::chrono::nanoseconds>(end1 - begin1).count() / 1e9; // s
		weight_S_MIRROR_onlyreduction = net_weight_PCSTPTG_single_bump(solu_MIRROR.first, solu_MIRROR.second, query_state_graph, alpha);
	}
	else {
		time_S_MIRROR_onlyreduction = 0;
		weight_S_MIRROR_onlyreduction = 0;
	}

	if (use_MIRROR_onlyBandB == true) {
		auto begin1 = std::chrono::high_resolution_clock::now();
		double x;
		pair<graph_hash_of_mixed_weighted, pair<int, int>> solu_MIRROR = accelerated_MIRROR
		({ input_time_interval.first, input_time_interval.second }, instance_graph, query_state_graph, alpha, x, 0, 1);
		auto end1 = std::chrono::high_resolution_clock::now();
		time_MIRROR_onlyBandB = std::chrono::duration_cast<std::chrono::nanoseconds>(end1 - begin1).count() / 1e9; // s
		weight_MIRROR_onlyBandB = net_weight_PCSTPTG_single_bump(solu_MIRROR.first, solu_MIRROR.second, query_state_graph, alpha);
	}
	else {
		time_MIRROR_onlyBandB = 0;
		weight_MIRROR_onlyBandB = 0;
	}

	if (use_S_MIRROR_onlyBandB == true) {
		auto begin1 = std::chrono::high_resolution_clock::now();
		double x, y;
		int w;
		pair<graph_hash_of_mixed_weighted, pair<int, int>> solu_MIRROR = accelerated_S_MIRROR
		({ input_time_interval.first, input_time_interval.second }, instance_graph, query_state_graph, alpha, x, w, h, y, 0, 1);
		auto end1 = std::chrono::high_resolution_clock::now();
		time_S_MIRROR_onlyBandB = std::chrono::duration_cast<std::chrono::nanoseconds>(end1 - begin1).count() / 1e9; // s
		weight_S_MIRROR_onlyBandB = net_weight_PCSTPTG_single_bump(solu_MIRROR.first, solu_MIRROR.second, query_state_graph, alpha);
	}
	else {
		time_S_MIRROR_onlyBandB = 0;
		weight_S_MIRROR_onlyBandB = 0;
	}




	if (use_Smart_ST == true) {
		auto begin3 = std::chrono::high_resolution_clock::now();
		pair<graph_hash_of_mixed_weighted, pair<int, int>> solu_Smart_ST = Smart_ST
		({ input_time_interval.first, input_time_interval.second }, instance_graph, query_state_graph, alpha);
		auto end3 = std::chrono::high_resolution_clock::now();
		time_Smart_ST = std::chrono::duration_cast<std::chrono::nanoseconds>(end3 - begin3).count() / 1e9; // s
		weight_Smart_ST = net_weight_PCSTPTG_single_bump(solu_Smart_ST.first, solu_Smart_ST.second, query_state_graph, alpha);
	}
	else {
		time_Smart_ST = 0;
		weight_Smart_ST = 0;
	}

	if (use_PCST == true) {
		auto begin3 = std::chrono::high_resolution_clock::now();
		pair<graph_hash_of_mixed_weighted, pair<int, int>> solu_PCST = PCST
		({ input_time_interval.first, input_time_interval.second }, instance_graph, query_state_graph, alpha);
		auto end3 = std::chrono::high_resolution_clock::now();
		time_PCST = std::chrono::duration_cast<std::chrono::nanoseconds>(end3 - begin3).count() / 1e9; // s
		weight_PCST = net_weight_PCSTPTG_single_bump(solu_PCST.first, solu_PCST.second, query_state_graph, alpha);
	}
	else {
		time_PCST = 0;
		weight_PCST = 0;
	}

	if (use_Random_ST == true) {
		auto begin4 = std::chrono::high_resolution_clock::now();
		pair<graph_hash_of_mixed_weighted, pair<int, int>> solu_Random_ST = Random_ST
		({ input_time_interval.first, input_time_interval.second }, instance_graph, query_state_graph, alpha, s);
		auto end4 = std::chrono::high_resolution_clock::now();
		time_Random_ST = std::chrono::duration_cast<std::chrono::nanoseconds>(end4 - begin4).count() / 1e9; // s
		weight_Random_ST = net_weight_PCSTPTG_single_bump(solu_Random_ST.first, solu_Random_ST.second, query_state_graph, alpha);
	}
	else {
		time_Random_ST = 0;
		weight_Random_ST = 0;
	}

	if (use_BF_ST == true) {
		auto begin5 = std::chrono::high_resolution_clock::now();
		pair<graph_hash_of_mixed_weighted, pair<int, int>> solu_BF_ST = BF_ST
		({ input_time_interval.first, input_time_interval.second }, instance_graph, query_state_graph, alpha, s);
		auto end5 = std::chrono::high_resolution_clock::now();
		time_BF_ST = std::chrono::duration_cast<std::chrono::nanoseconds>(end5 - begin5).count() / 1e9; // s
		weight_BF_ST = net_weight_PCSTPTG_single_bump(solu_BF_ST.first, solu_BF_ST.second, query_state_graph, alpha);
	}
	else {
		time_BF_ST = 0;
		weight_BF_ST = 0;
	}





}
#pragma endregion load_algorithms

/*global data*/
graph_hash_of_mixed_weighted NY_instance_graph, NY_query_state_graph, R_instance_graph, R_query_state_graph, W_instance_graph, W_query_state_graph;
int global_NY_loaded = 0, global_R_loaded = 0, global_W_loaded = 0;

#pragma region
void load_global_data(string data_name) {

	if (data_name == "NY") {
		if (global_NY_loaded == 0) {
			global_NY_loaded = 1;

			std::unordered_map<int, pair<double, double>> read_intersection_lon_and_lat;
			read_road_data(NY_instance_graph, "NY", read_intersection_lon_and_lat);

			/*read initial_query_state_graph for £¡ days*/
			bool count_pickup = true, count_dropoff = false;
			for (int i = 1; i <= 31; i++) {
				read_taxi_data_in_a_day_precision_hour(NY_query_state_graph, "NY", i, count_pickup, count_dropoff); // ith day from day_ID
			}

			global_NY_loaded = 2;
		}
		else {
			while (global_NY_loaded != 2) { // is not loaded yet
				; // wait until loaded
			}
		}	
	}
	else if (data_name == "Wiki") {
		if (global_W_loaded == 0) {
			global_W_loaded = 1;

			/*read graph*/
			std::unordered_map<int, string> page_names;
			read_Wiki_graph_data(W_instance_graph, page_names);

			/*read initial_query_state_graph for £¡ days*/
			for (int i = 1; i <= 31; i++) {
				read_Wiki_pageview_data_in_a_day_precision_hour(W_query_state_graph, i);
			}

			global_W_loaded = 2;
		}
		else {
			while (global_W_loaded != 2) { // is not loaded yet
				; // wait until loaded
			}
		}
	}
	else if (data_name == "Reddit") {
		if (global_R_loaded == 0) {
			global_R_loaded = 1;

			/*read graph*/
			read_Reddit_graph_data(R_instance_graph);

			/*read initial_query_state_graph for £¡ days*/
			for (int i = 1; i <= 30; i++) {
				read_Reddit_comment_data_in_a_day_precision_hour(R_query_state_graph, i);
			}

			global_R_loaded = 2;
		}
		else {
			while (global_R_loaded != 2) { // is not loaded yet
				; // wait until loaded
			}
		}	
	}
}
#pragma endregion load_global_data

#pragma region
void experiment_element(string data_name, string save_name, int V, int m, double alpha, double p, double q, bool intensive_query, int iteration_times, int h, int depth, int s,
	bool use_MIRROR, bool use_S_MIRROR, bool use_H_MIRROR, bool use_H_S_MIRROR, bool use_MIRROR_Basic, bool use_S_MIRROR_Basic,
	bool use_Smart_ST, bool use_Random_ST, bool use_BF_ST, bool use_PCST, bool use_MIRROR_onlyreduction, bool use_S_MIRROR_onlyreduction, bool use_MIRROR_onlyBandB, bool use_S_MIRROR_onlyBandB) {

	/*output*/
	ofstream outputFile;
	outputFile.precision(6);
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);
	outputFile.open(save_name);
	outputFile << "queied_time_subinterval.first,V,m,alpha,p,q,intensive_query,h,depth,s,"
		<< "time_MIRROR,weight_MIRROR,time_S_MIRROR,weight_S_MIRROR,"
		<< "time_H_MIRROR,weight_H_MIRROR,time_H_S_MIRROR,weight_H_S_MIRROR,"
		<< "time_MIRROR_Basic,weight_MIRROR_Basic,time_S_MIRROR_Basic,weight_S_MIRROR_Basic,"
		<< "time_Smart_ST,weight_Smart_ST,time_Random_ST,weight_Random_ST,time_BF_ST,weight_BF_ST,time_PCST,weight_PCST,"
		<< "MIRROR_UB,S_MIRROR_UB,MIRROR_Basic_UB,S_MIRROR_Basic_UB,"
		<< "time_MIRROR_onlyreduction,weight_MIRROR_onlyreduction,time_S_MIRROR_onlyreduction,weight_S_MIRROR_onlyreduction,"
		<< "time_MIRROR_onlyBandB,weight_MIRROR_onlyBandB,time_S_MIRROR_onlyBandB,weight_S_MIRROR_onlyBandB" << endl;

	/*read data*/
	graph_hash_of_mixed_weighted x, y;
	graph_hash_of_mixed_weighted* old_instance_graph = &x;
	graph_hash_of_mixed_weighted* old_query_state_graph = &y;
	int max_m;
	if (data_name == "NY") {	
		old_instance_graph = &NY_instance_graph;
		old_query_state_graph = &NY_query_state_graph;
		max_m = 24 * 31; // ! days
	}
	else if (data_name == "Wiki") {
		old_instance_graph = &W_instance_graph;
		old_query_state_graph = &W_query_state_graph;
		max_m = 24 * 31; // ! days
	}
	else if (data_name == "Reddit") {
		old_instance_graph = &R_instance_graph;
		old_query_state_graph = &R_query_state_graph;
		max_m = 24 * 30; // ! days
	}

	int original_V = (*old_instance_graph).hash_of_vectors.size();
	

	/*start random experiments*/
	for (int itera = 0; itera < iteration_times; itera++) {
		cout << save_name << " itera: " << itera << endl;

		graph_hash_of_mixed_weighted instance_graph;
		if (V < original_V) {
			unordered_set<int> selected_vertices = graph_hash_of_mixed_weighted_breadth_first_search_a_fixed_number_of_vertices_in_unconnected_graphs_start_from_maxcpn(*old_instance_graph, V);
			instance_graph = graph_hash_of_mixed_weighted_extract_subgraph_for_a_hash_of_vertices(*old_instance_graph, selected_vertices);
		}
		else {
			instance_graph = graph_hash_of_mixed_weighted_copy_graph(*old_instance_graph);
		}

		/*randomly query time interval*/
		graph_hash_of_mixed_weighted query_state_graph;
		pair<int, int> queied_time_subinterval;
		if (intensive_query) {
			boost::random::uniform_int_distribution<> dist{ 0, max_m - m }; // generating random number in [0, max_m - m]
			int rand = dist(boost_random_time_seed);
			queied_time_subinterval = { time_ID_start + rand, time_ID_start + rand + m - 1 };
			query_state_graph = produce_small_query_state_graph_intensive(*old_query_state_graph, instance_graph, p, time_ID_start + rand, time_ID_start + rand + m - 1); // top query_percent% queried
		}
		else {
			boost::random::uniform_int_distribution<> dist{ 24, max_m - m }; // generating random number in [24, max_m - m]
			int rand = dist(boost_random_time_seed);
			queied_time_subinterval = { time_ID_start + rand, time_ID_start + rand + m - 1 };
			query_state_graph = produce_small_query_state_graph_abnormal(*old_query_state_graph, instance_graph, q, time_ID_start + rand, time_ID_start + rand + m - 1); // top query_percent% queried
		}






		//cout << "graph_hash_of_mixed_weighted_num_edges(query_state_graph): " << graph_hash_of_mixed_weighted_num_edges(query_state_graph) << endl;
		//graph_hash_of_mixed_weighted_print(instance_graph);
		//graph_hash_of_mixed_weighted_print(query_state_graph);

		double time_MIRROR, weight_MIRROR, time_S_MIRROR, weight_S_MIRROR,
			time_H_MIRROR, weight_H_MIRROR, time_H_S_MIRROR, weight_H_S_MIRROR,
			time_MIRROR_Basic, weight_MIRROR_Basic, time_S_MIRROR_Basic, weight_S_MIRROR_Basic,
			time_Smart_ST, weight_Smart_ST, time_Random_ST, weight_Random_ST, time_BF_ST, weight_BF_ST, time_PCST, weight_PCST,
			time_MIRROR_onlyreduction, weight_MIRROR_onlyreduction, time_S_MIRROR_onlyreduction, weight_S_MIRROR_onlyreduction,
			time_MIRROR_onlyBandB, weight_MIRROR_onlyBandB, time_S_MIRROR_onlyBandB, weight_S_MIRROR_onlyBandB;

		int reduced_V;
		double MIRROR_for_upper_bound, kappa_1, kappa_2, MIRROR_Basic_for_upper_bound, S_MIRROR_Basic_for_upper_bound;

		load_algorithms(queied_time_subinterval, instance_graph, query_state_graph, alpha, h, depth, s,
			time_MIRROR, weight_MIRROR, time_S_MIRROR, weight_S_MIRROR,
			time_H_MIRROR, weight_H_MIRROR, time_H_S_MIRROR, weight_H_S_MIRROR,
			time_MIRROR_Basic, weight_MIRROR_Basic, time_S_MIRROR_Basic, weight_S_MIRROR_Basic,
			time_Smart_ST, weight_Smart_ST, time_Random_ST, weight_Random_ST,
			time_BF_ST, weight_BF_ST, time_PCST, weight_PCST,
			MIRROR_for_upper_bound, kappa_1, kappa_2, reduced_V, MIRROR_Basic_for_upper_bound, S_MIRROR_Basic_for_upper_bound,
			use_MIRROR, use_S_MIRROR, use_H_MIRROR, use_H_S_MIRROR, use_MIRROR_Basic, use_S_MIRROR_Basic, use_Smart_ST, use_Random_ST, use_BF_ST, use_PCST,
			time_MIRROR_onlyreduction, weight_MIRROR_onlyreduction, time_S_MIRROR_onlyreduction, weight_S_MIRROR_onlyreduction,
			time_MIRROR_onlyBandB, weight_MIRROR_onlyBandB, time_S_MIRROR_onlyBandB, weight_S_MIRROR_onlyBandB,
			use_MIRROR_onlyreduction, use_S_MIRROR_onlyreduction, use_MIRROR_onlyBandB, use_S_MIRROR_onlyBandB);

		double MIRROR_UB = (2 * weight_MIRROR + MIRROR_for_upper_bound) / 2;
		double MIRROR_Basic_UB = (2 * weight_MIRROR_Basic + MIRROR_Basic_for_upper_bound) / 2;

		double S_MIRROR_UB = produce_S_MIRROR_UB(queied_time_subinterval, instance_graph, query_state_graph, alpha, reduced_V, weight_S_MIRROR, kappa_1, kappa_2);
		double S_MIRROR_Basic_UB = 2 * weight_S_MIRROR_Basic + S_MIRROR_Basic_for_upper_bound + instance_graph.hash_of_vectors.size();

		outputFile << queied_time_subinterval.first << "," << V << "," << m << "," << alpha << "," << p << "," <<
			q << "," << intensive_query << "," << h << "," << depth << "," << s << "," <<
			time_MIRROR << "," << weight_MIRROR << "," <<
			time_S_MIRROR << "," << weight_S_MIRROR << "," <<
			time_H_MIRROR << "," << weight_H_MIRROR << "," <<
			time_H_S_MIRROR << "," << weight_H_S_MIRROR << "," <<
			time_MIRROR_Basic << "," << weight_MIRROR_Basic << "," <<
			time_S_MIRROR_Basic << "," << weight_S_MIRROR_Basic << "," <<
			time_Smart_ST << "," << weight_Smart_ST << "," <<
			time_Random_ST << "," << weight_Random_ST << "," <<
			time_BF_ST << "," << weight_BF_ST << "," <<
			time_PCST << "," << weight_PCST << "," <<
			MIRROR_UB << "," << S_MIRROR_UB << "," <<
			MIRROR_Basic_UB << "," << S_MIRROR_Basic_UB << "," <<
			time_MIRROR_onlyreduction << "," << weight_MIRROR_onlyreduction << "," <<
			time_S_MIRROR_onlyreduction << "," << weight_S_MIRROR_onlyreduction << "," <<
			time_MIRROR_onlyBandB << "," << weight_MIRROR_onlyBandB << "," <<
			time_S_MIRROR_onlyBandB << "," << weight_S_MIRROR_onlyBandB << endl;

	}
	outputFile.close();

}
#pragma endregion experiment_element

#pragma region
void example_experiments() {

	/*New York*/
	if (1) {

		load_global_data("NY"); // this is the load the data before experiments; this can be load_global_data("Reddit"); or load_global_data("Wiki");

		int iteration_times = 10;
		bool intensive_query = true;

		int V = 77580, m = 72, h = 1, depth = 1, s = 10;
		double alpha = 1, p = 1, q = 0;

		bool use_MIRROR = 1, use_S_MIRROR = 1, use_H_MIRROR = 1, use_H_S_MIRROR = 1, use_MIRROR_Basic = 0, use_S_MIRROR_Basic = 0, use_Smart_ST = 1, use_Random_ST = 1, use_BF_ST = 1, use_PCST = 1;


		/*
		what does the following code means?

		void experiment_element(string data_name, string save_name, int V, int m, double alpha, double p, double q, bool intensive_query, int iteration_times, int h, int depth, int s,
	bool use_MIRROR, bool use_S_MIRROR, bool use_H_MIRROR, bool use_H_S_MIRROR, bool use_MIRROR_Basic, bool use_S_MIRROR_Basic,
	bool use_Smart_ST, bool use_Random_ST, bool use_BF_ST, bool use_PCST, bool use_MIRROR_onlyreduction, bool use_S_MIRROR_onlyreduction, bool use_MIRROR_onlyBandB, bool use_S_MIRROR_onlyBandB);


	experiment_element is a function that run experiments in our paper. The input values of this function are as follows:

	data_name: can be "NY", "Wiki", or "Reddit", this is to choose which data to run

	save_name: if save_name is "experiment_NY_base.csv", then the experiment results (solutions, running times of different algorithms) are recorded in the file "experiment_NY_base.csv"

	V: number of vertices to run (if V is smaller than the maximum number of vertices in data, then it will randomly find V vertices via a breadth first search, and run the searched vertices)

	m: number of time slots

	alpha: regulating weight of temporal discrepancy (see the supplement)

	p: percentage of queries vertices in each time slot in our experiments

	q: abnormally increased percentage in our case studies for abnormally increasing activities associated with vertices

	intensive_query: if true, then use p to do experiments, otherwise use q

	iteration_times: how many times to do random experiments

	h: in S-MIRROR and H-S-MIRROR, h*m*log(m) time sub-intervals are randomly selected in Omiga_3. (in our paper, we set h=1)

	depth: the parameter b in our supplement (the search depth in H-MIRROR and H-S-MIRROR)

	s: the parameter in BF-ST and Random-ST

	use_MIRROR ... use_S_MIRROR_onlyBandB: whether to use the algorithm MIRROR ... S_MIRROR_onlyBandB

		*/

		experiment_element("NY", "experiment_NY_base.csv", V, m, alpha, p, q, intensive_query, iteration_times, h, depth, s,
			use_MIRROR, use_S_MIRROR, use_H_MIRROR, use_H_S_MIRROR, use_MIRROR_Basic, use_S_MIRROR_Basic, use_Smart_ST, use_Random_ST, use_BF_ST, use_PCST, 0, 0, 0, 0);
	}



}
#pragma endregion example_experiments


int main()
{
	/*the two values below are for #include <graph_hash_of_mixed_weighted.h>*/
	graph_hash_of_mixed_weighted_turn_on_value = 1e3;
	graph_hash_of_mixed_weighted_turn_off_value = 1e1;

	srand(time(NULL)); //  seed random number generator   

	auto begin = std::chrono::high_resolution_clock::now();

	example_experiments();

	auto end = std::chrono::high_resolution_clock::now();
	double runningtime = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e9; // s


	cout << "END    runningtime: " << runningtime << "s" << endl;
}