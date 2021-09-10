/*


Implementing Johnson's Algorithm on a Directed/Undirected & Weighted Graph using different data structures to implement the Dijkstra's Algorithm Subpart


The four different data structures used to implement (and compare performance) on Dijkstra's Algorithm are :
1. A simple array
2. A Binary Heap (implemented using an array)
3. A Binomial Heap (implemented using pointers)
4. A Fibonacci Heap (implemented using pointers)


Basic Walkthrough of the Code :
1. Represent the graph by reading the input into an adjacency list.
2. Create a dummy node (reprsented by 'n+1' in the adjacency list), and add one edge from this to each vertex, each with weight 0.
3. Run Bellman Ford's Algorithm on this new adjacency list with the dummy node as source. Dist from dummy node to each vetex represents that vertex's vertex weight (h[v]).
4. Dijkstra's Algorithm is run on the modified graph where each edge (from u->v) is reweighted from w -> w + h[v] - h[u].
5. Dijkstra's Algorithm in essence is the same among all data structures, but the way decrease_key & extract_min is performed is completely different.
6. Final shortest path from u -> v is given as (dist from Dijkstra's Algorithm) + (correction on reweighting).


*/



//Importing all the required libraries
#include <iostream>
#include <string>
#include <vector>
#include <stack>
#include <queue>
#include <utility>
#include <set>
#include <cmath>
#include <cstdio>
#include <ctime>
using namespace std ;


//Defining the way to store edges in an adjacency list
//Edge from u->v with weight w represented as graph[u] points to {v,w}
typedef pair<int,int> edge ;


//Initializing the structure for a node in a binomial heap
struct binheap_node{

	long long int vertex, dist ;
	int degree ;
	binheap_node *parent, *child, *sibling ;

} ;


//Initializing the structure for a node in a fibonacci heap
struct fibheap_node{

	long long int vertex, dist ;
	int rank, marked ;
	fibheap_node *parent, *child, *left, *right  ;

} ;


//Reading the input data and storing it (the graph representation) in an adjacency list
void create_adjacency_weighted_list(vector<edge> *graph, long long int n, int d, int *neg_weight_cycle){

	for(long long int i=1 ; i<=n ; i++){
		for(long long int j=1 ; j<=n ; j++){
			int w ;
			cin >> w ;
			if(w!=999999 && i!=j){
				graph[i].push_back(make_pair(j,w)) ;
				if(d==0 && w<0){
					*neg_weight_cycle = 1 ;
				}
			}
		}
	}

}


//Deleting the graph's adjacency list after running that test case
void delete_weighted_graph(vector<edge> *graph, long long int n){

	for(long long int i=0 ; i<=n; i++){
		for(long long int j=0 ; j<graph[i].size() ; j++){
			graph[i].erase(graph[i].begin()) ;
		}
	}

}


//Reweighting the edges in the graph's adjacency list as per the new vertex weights found using Johnson's Algorithm
void reweight_graph(vector<edge> *graph, vector<edge> *graph_new, long long int dist_array[], long long int n){

	for(long long int u=1 ; u<=n ; u++){
		for(auto j=graph[u].begin() ; j!=graph[u].end() ; ++j){
			int v=j->first, w=j->second ;
			int w_new = w + dist_array[u] - dist_array[v] ;
			graph_new[u].push_back(make_pair(v,w_new)) ;
		}
	}

}


//Used to store the binary number representation of the number of verticies in an array
void make_binary_number(int bin_num[], int *log_value, long long int n){

	int i=0 ;
	while(n>0){
		bin_num[i] = n%2 ;
		n = n/2 ;
		i++ ;
	}
	*log_value = i-1 ;

}


//Returns a binomial tree of specified degree. The vertex values and associated distances are all initialized with [1,n] & 999999 (during initialization)
binheap_node *construct_bintree(vector<binheap_node *> &heap, long long int *node_counter, int degree){

	binheap_node *node = new binheap_node ;
	node->dist = 999999 ;
	node->vertex = *node_counter ;
	heap[*node_counter] = node ;
	(*node_counter)++ ;
	node->degree = degree ;
	node->parent = NULL ;
	node->child = NULL ;
	node->sibling = NULL ;
	if(degree>0){
		node->child = construct_bintree(heap,node_counter,0) ;
		binheap_node *child_node = node->child ;
		int dummy_degree = 1 ;
		while(dummy_degree < degree){
			child_node->sibling = construct_bintree(heap,node_counter,dummy_degree) ;
			child_node = child_node->sibling ;
			dummy_degree++ ;
		}
	}
	binheap_node *child_node = node->child ;
	int child_degree = 0 ;
	while(child_degree < degree){
		child_node->parent = node ;
		child_node = child_node->sibling ;
		child_degree++ ;
	}
	return node ;

}


//Used to initialize a binomial heap by constructing binomial trees of specified degrees as per the binary representation of number of verticies
void construct_binheap(vector<binheap_node *> &heap, vector<binheap_node *> &tree_roots, long long int *node_counter, int bin_num[], int log_value, int index){

	if(index > log_value){
		return ;
	}
	else if(bin_num[index]==0){
		construct_binheap(heap,tree_roots,node_counter,bin_num,log_value,index+1) ;
	}
	else{
		tree_roots[index] = construct_bintree(heap,node_counter,index) ;
		construct_binheap(heap,tree_roots,node_counter,bin_num,log_value,index+1) ;
	}


}


//Used to merge two binomial trees of the heap after deleting a node during the extract_min operation
binheap_node *merge_two_trees(binheap_node *node1, binheap_node *node2){

	if(node1->degree == 0){
		node1->child = node2 ;
		node2->parent = node1 ;
		node2->sibling = NULL ;
		(node1->degree)++ ;
		return node1 ;
	}
	binheap_node *node1_child = node1->child ;
	while(node1_child->sibling!=NULL){
		node1_child = node1_child->sibling ;
	}
	node2->sibling = NULL ;
	node2->parent = node1 ;
	node1_child->sibling = node2 ;
	(node1->degree)++ ;
	return node1 ;

}


//In the extract_min operation, this function is used to merge all the childen of the deleted node into the root list
void adjust_trees(vector<binheap_node *> &heap, vector<binheap_node *> &tree_roots, binheap_node *node_child){

	int degree = node_child->degree ;
	while(tree_roots[degree]!=NULL){
		binheap_node *tree_node = tree_roots[degree] ;
		if(node_child->dist < tree_node->dist){
			node_child = merge_two_trees(node_child,tree_node);
		}
		else{
			node_child = merge_two_trees(tree_node,node_child);
		}
		tree_roots[degree] = NULL ;
		degree++ ;
	}
	tree_roots[degree] = node_child ;
	node_child->parent = NULL ;
	node_child->sibling = NULL ;

}


//Used to initialize a tree for the fibonacci heap
fibheap_node *construct_fibheap_1(vector<fibheap_node *> &heap, long long int *node_counter, int rank){

	fibheap_node *node = new fibheap_node ;
	fibheap_node *child_node = NULL ;
	node->dist = 999999 ;
	node->vertex = *node_counter ;
	heap[*node_counter] = node ;
	(*node_counter)++ ;
	node->rank = rank ;
	node->marked = 0 ;
	node->parent = NULL ;
	node->child = NULL ;
	node->left = NULL ;
	node->right = NULL ;
	if(rank>0){
		node->child = construct_fibheap_1(heap,node_counter,0) ;
		child_node = node->child ;
		int dummy_rank = 1 ;
		while(dummy_rank < rank){
			child_node->right = construct_fibheap_1(heap,node_counter,dummy_rank) ;
			(child_node->right)->left = child_node ;
			child_node = child_node->right ;
			dummy_rank++ ;
		}
	}
	child_node = node->child ;
	int child_rank = 0 ;
	while(child_rank < rank){
		child_node->parent = node ;
		child_node = child_node->right ;
		child_rank++ ;
	}
	return node ;

}


//Joins all the trees to the root list to make the fibonacci heap
void construct_fibheap_2(vector<fibheap_node *> &heap, vector<fibheap_node *> &tree_roots, long long int *node_counter, int bin_num[], int log_value, int index){

	if(index > log_value){
		return ;
	}
	else if(bin_num[index]==0){
		construct_fibheap_2(heap,tree_roots,node_counter,bin_num,log_value,index+1) ;
	}
	else{
		tree_roots[index] = construct_fibheap_1(heap,node_counter,index) ;
		construct_fibheap_2(heap,tree_roots,node_counter,bin_num,log_value,index+1) ;
	}

}


//Used to make the root list of the initialized root list a circular doubly linked list. heap[0] represents a pointer to the minimum distance node
void modify_fibheap(vector<fibheap_node *> &heap, vector<fibheap_node *> &tree_roots, int bin_num[], int log_value){

	int j=0 ;
	fibheap_node *node1 = NULL ;
	for(int i=0 ; i<=log_value ; i++){
		if(bin_num[i]==1 && j==0){
			node1 = tree_roots[i] ;
			heap[0] = node1 ;
			j++ ;
		}
		else if(bin_num[i]==1){
			fibheap_node *node2 = tree_roots[i] ;
			node1->right = node2 ;
			node2->left = node1 ;
			node1 = node2 ;
		}
	}
	node1->right = heap[0] ;
	(heap[0])->left = node1 ;

}


//Used in fibonacci heaps to add nodes recursively to the root list
//During decrease_key (decrease_key = 1), used to bring the node (and further, marked parent nodes) to the root list
//During extract_min (decrease_key = 0), used to bring the children to the to be deleted node to the root list
void add_node_to_root_list(vector<fibheap_node *> &heap, vector<fibheap_node *> &tree_roots, long long int vertex, int decrease_key){

	fibheap_node *node = heap[vertex] ;
	if((node->parent)==NULL){
		return ;
	}
	fibheap_node *node_parent = node->parent ;
	fibheap_node *node_right = node->right ;
	if((node->left) == NULL){
		node_parent->child = node_right ;
		if((node_right) != NULL){
			(node_right)->left = NULL ;
		}
		node->right = NULL ;
	}
	else{
		(node->left)->right = node_right ;
		if((node_right) != NULL){
			(node_right)->left = node->left ;
		}
		node->left = NULL ;
		node->right = NULL ;
	}
	node_parent->rank += -1 ;
	node->parent = NULL ;
	node->right = (heap[0])->right ;
	node->left = (heap[0]) ;
	(node->right)->left = node ;
	(heap[0])->right = node ;
	if((node->dist < (heap[0])->dist) || ((node->dist <= (heap[0])->dist) && (node->vertex < (heap[0])->vertex))){
		heap[0] = node ;
	}
	if(decrease_key==1){
		if(node_parent->marked == 0){
			node_parent->marked = 1 ;
			return ;
		}
		else{
			add_node_to_root_list(heap,tree_roots,node_parent->vertex,1) ;
		}
	}
	else{
		if(node_right == NULL){
			return ;
		}
		else{
			add_node_to_root_list(heap,tree_roots,node_right->vertex,0) ;
		}
	}

}


//Used to merge two trees of the same rank while consolidating the fibonacci heap during extract_min operation
void merge_trees_fib(vector<fibheap_node *> &heap, vector<fibheap_node *> &tree_roots, fibheap_node *node1){

	int rank = node1->rank ;
	fibheap_node *node2 = tree_roots[rank] ;
	if(node2 == NULL){
		tree_roots[rank] = node1 ;
		node1->parent = NULL ;
		node1->left = NULL ;
		node1->right = NULL ;
		return ;
	}
	else{
		tree_roots[rank] = NULL ;
		if(node1->dist < node2->dist){
			node2->left = NULL ;
			node2->right = node1->child ;
			node2->parent = node1 ;
			if((node1->child)!=NULL){
				(node1->child)->left = node2 ;
			}
			node1->child = node2 ;
			(node1->rank)++ ;
			node1->parent = NULL ;
			node1->left = NULL ;
			node1->right = NULL ;
			merge_trees_fib(heap,tree_roots,node1) ;
		}
		else{
			node1->left = NULL ;
			node1->right = node2->child ;
			node1->parent = node2 ;
			if((node2->child)!=NULL){
				(node2->child)->left = node1 ;
			}
			node2->child = node1 ;
			(node2->rank)++ ;
			node2->parent = NULL ;
			node2->left = NULL ;
			node2->right = NULL ;
			merge_trees_fib(heap,tree_roots,node2) ;
		}
	}

}


//After merging the trees of the same rank while consolidating the fibonacci heap, this functions make the root list circular again
void make_heap_circular(vector<fibheap_node *> &heap, vector<fibheap_node *> &tree_roots, long long int n){

	int i=0, j=0 ;
	heap[0] = NULL ;
	fibheap_node *node1, *start = NULL ;
	while(i<=n){
		if(tree_roots[i]!=NULL){
			if(j==0){
				start = tree_roots[i] ;
				heap[0] = tree_roots[i] ;
				node1 = tree_roots[i] ;
				i++ ;
				j++ ;
				continue ;
			}
			else{
				fibheap_node *node2 = node1 ;
				node1 = tree_roots[i] ;
				node1->left = node2 ;
				node2->right = node1 ;
				if((node1->dist < (heap[0])->dist) || ((node1->dist <= (heap[0])->dist) && (node1->vertex < (heap[0])->vertex))){
					heap[0] = node1 ;
				}
				i++ ;
				continue ;
			}
		}
		else{
			i++ ;
		}
	}
	if(node1==NULL){
		return ;
	}
	if((node1->left)==NULL){
		node1->left = node1 ;
		node1->right = node1 ;
		return ;
	}
	node1->right = start ;
	start->left = node1 ;

}


//Used to consolidate the fibonacci heap (part 2 of extract_min operation of the fibonacci heap)
void consolidate_heap(vector<fibheap_node *> &heap, vector<fibheap_node *> &tree_roots, long long int n){

	fibheap_node *head_left = (heap[0])->left ;
	head_left->right = NULL ;
	(heap[0])->left = NULL ;
	fibheap_node *node1 = heap[0] ;
	heap[0] = NULL ;
	while(node1!=NULL){
		fibheap_node *node2 = node1 ;
		node1 = node1->right ;
		node2->left = NULL ;
		node2->right = NULL ;
		merge_trees_fib(heap,tree_roots,node2) ;
	}
	make_heap_circular(heap,tree_roots,n) ;

}


//Performs the decrease_key opeartion while performing Dijkstra's algorithm by maintaining an array
void decrease_key_array(long long int arr[][2], long long int indexes[], long long int index, long long int new_value){

	arr[index][1] = new_value ;
	for(long long int i=index ; i>0 ; i--){
		if((arr[i][1] < arr[i-1][1]) || ((arr[i][1] <= arr[i-1][1]) && (arr[i][0] < arr[i-1][0]))){
			long long int temp0 = arr[i][0], temp1 = arr[i][1] ;
			arr[i][0] = arr[i-1][0] ;
			arr[i][1] = arr[i-1][1] ;
			arr[i-1][0] = temp0 ;
			arr[i-1][1] = temp1 ; 
			indexes[arr[i][0]] = i ;
			indexes[arr[i-1][0]] = i-1 ;
		}
		else{
			break ;
		}
	}

}


//Performs the decrease_key opeartion while performing Dijkstra's algorithm by maintaining a binary heap
void decrease_key_binary_heap(long long int arr[][2], long long int indexes[], long long int index, long long int new_value){

	arr[index][1] = new_value ;
	long long int i = index ;
	while(i>0){
		long long int j=0 ;
		if((i%2)==0){
			j = (i/2) -1 ;
		}
		else{
			j = i/2 ;
		}
		if((arr[i][1] < arr[j][1]) || ((arr[i][1] <= arr[j][1]) && (arr[i][0] < arr[j][0]))){
			long long int temp0 = arr[i][0], temp1 = arr[i][1] ;
			arr[i][0] = arr[j][0] ;
			arr[i][1] = arr[j][1] ;
			arr[j][0] = temp0 ;
			arr[j][1] = temp1 ; 
			indexes[arr[i][0]] = i ;
			indexes[arr[j][0]] = j ;
			i = j ;
		}
		else{
			break ;
		}
	}

}


//Performs the decrease_key opeartion while performing Dijkstra's algorithm by maintaining a binomial heap
void decrease_key_binomial_heap(vector<binheap_node *> &heap, binheap_node **head, long long int vertex, long long int new_val){

	binheap_node *node = heap[vertex] ;
	node->dist = new_val ;
	while(node->parent!=NULL){
		if(((node->parent)->dist < new_val) || (((node->parent)->dist <= new_val) && ((node->parent)->vertex < node->vertex))){
			break ;
		}
		binheap_node *node_parent = node->parent ;
		long long int parent_dist = node_parent->dist, parent_vertex = node_parent->vertex ;
		long long int node_degree = node->degree ;
		heap[vertex] = node_parent ;
		heap[parent_vertex] = node ;
		node_parent->dist = new_val, node_parent->vertex = vertex ;
		node->dist = parent_dist, node->vertex = parent_vertex ;
		node = node->parent ;
	}
	if((new_val < (*head)->dist) || ((node->dist <= (*head)->dist) && (node->vertex < (*head)->vertex))){
		*head = node ;
	}

}


//Performs the decrease_key opeartion while performing Dijkstra's algorithm by maintaining a fibonacci heap
void decrease_key_fibheap(vector<fibheap_node *> &heap, vector<fibheap_node *> &tree_roots, long long int vertex, long long int new_val){

	fibheap_node *node = heap[vertex] ;
	node->dist = new_val ;
	if((node->parent) == NULL){
		if((node->dist < (heap[0])->dist) || ((node->dist <= (heap[0])->dist) && (node->vertex < (heap[0])->vertex))){
			heap[0] = node ;
		}
		return ;
	}
	else if((new_val > (node->parent)->dist) || ((new_val >= (node->parent)->dist) && ((node->parent)->vertex < node->vertex))){
		return ;
	}
	else{
		add_node_to_root_list(heap,tree_roots,vertex,1) ;
	}

}


//Performs the extract_min opeartion while performing Dijkstra's algorithm by maintaining an array
void extract_min_array(long long int arr[][2], long long int indexes[], long long int last_index){

	long long int min0 = arr[0][0], min1 = arr[0][1] ;
	arr[0][0] = arr[last_index][0] ;
	arr[0][1] = arr[last_index][1] ;
	arr[last_index][0] = min0 ;
	arr[last_index][1] = min1 ;
	indexes[arr[last_index][0]] = last_index ;
	indexes[arr[0][0]] = 0 ;
	for(long long int i=0 ; i<last_index-1 ; i++){
		if((arr[i][1] > arr[i+1][1]) || (arr[i][1] >= arr[i+1][1]) && (arr[i][0] > arr[i+1][0])){
			long long int temp0 = arr[i][0], temp1 = arr[i][1] ;
			arr[i][0] = arr[i+1][0] ;
			arr[i][1] = arr[i+1][1] ;
			arr[i+1][0] = temp0 ;
			arr[i+1][1] = temp1 ; 
			indexes[arr[i][0]] = i ;
			indexes[arr[i+1][0]] = i+1 ;
		}
		else{
			break ;
		}
	}

}


//Performs the extract_min opeartion while performing Dijkstra's algorithm by maintaining a binary heap
void extract_min_binary_heap(long long int arr[][2], long long int indexes[], long long int last_index){

	long long int min0 = arr[0][0], min1 = arr[0][1] ;
	arr[0][0] = arr[last_index][0] ;
	arr[0][1] = arr[last_index][1] ;
	arr[last_index][0] = min0 ;
	arr[last_index][1] = min1 ;
	indexes[arr[last_index][0]] = last_index ;
	indexes[arr[0][0]] = 0 ;
	long long int i=0 ;
	while(i<last_index){
		long long int l=2*i+1, r=2*i+2 ;
		if(l >= last_index){
			break ;
		}
		if((r >= last_index) && ((arr[l][1] < arr[i][1]) || ((arr[l][1] <= arr[i][1]) && (arr[l][0] < arr[i][0])))){
			long long int temp0 = arr[i][0], temp1 = arr[i][1] ;
			arr[i][0] = arr[l][0] ;
			arr[i][1] = arr[l][1] ;
			arr[l][0] = temp0 ;
			arr[l][1] = temp1 ; 
			indexes[arr[i][0]] = i ;
			indexes[arr[l][0]] = l ;
			i = l ;
			continue ;
		}
		if(((arr[l][1] < arr[r][1]) || ((arr[l][1] <= arr[r][1]) && (arr[l][0] < arr[r][0]))) && ((arr[l][1] < arr[i][1]) || ((arr[l][1] <= arr[i][1]) && (arr[l][0] < arr[i][0])))){
			long long int temp0 = arr[i][0], temp1 = arr[i][1] ;
			arr[i][0] = arr[l][0] ;
			arr[i][1] = arr[l][1] ;
			arr[l][0] = temp0 ;
			arr[l][1] = temp1 ; 
			indexes[arr[i][0]] = i ;
			indexes[arr[l][0]] = l ;
			i = l ;
			continue ;
		}
		if(r >= last_index){
			break ;
		}
		if(((arr[r][1] < arr[l][1]) || ((arr[r][1] <= arr[l][1]) && (arr[r][0] < arr[l][0]))) && ((arr[r][1] < arr[i][1]) || ((arr[r][1] <= arr[i][1]) && (arr[r][0] < arr[i][0])))){
			long long int temp0 = arr[i][0], temp1 = arr[i][1] ;
			arr[i][0] = arr[r][0] ;
			arr[i][1] = arr[r][1] ;
			arr[r][0] = temp0 ;
			arr[r][1] = temp1 ; 
			indexes[arr[i][0]] = i ;
			indexes[arr[r][0]] = r ;
			i = r ;
			continue ;
		}
		break ;
	}

}


//Performs the extract_min opeartion while performing Dijkstra's algorithm by maintaining a binomial heap
void extract_min_binomial_heap(vector<binheap_node *> &heap, vector<binheap_node *> &tree_roots, pair<long long int, long long int> &min_node_data, binheap_node **head, int log_val){

	binheap_node *del_node = *head ;
	min_node_data = make_pair(del_node->vertex, del_node->dist) ;
	*head = NULL ;
	int head_null = 0 ;
	heap[del_node->vertex] = NULL ;
	tree_roots[del_node->degree] = NULL ;
	binheap_node *node_child = del_node->child ;
	del_node->child = NULL ;
	while(node_child!=NULL){
		node_child->parent = NULL ;
		binheap_node *node_child_copy = node_child ;
		node_child = node_child->sibling ;
		adjust_trees(heap,tree_roots,node_child_copy) ;
	}
	delete del_node ;
	for(int i=0 ; i<=log_val ; i++){
		if(tree_roots[i]!=NULL && head_null==0){
			*head = tree_roots[i] ;
			head_null++ ;
		}
		else if((tree_roots[i]!=NULL) && (((tree_roots[i])->dist < (*head)->dist) || (((tree_roots[i])->dist <= (*head)->dist) && ((tree_roots[i])->vertex < (*head)->vertex)))){
			*head = tree_roots[i] ;
		}
	}

}


//Performs the extract_min opeartion while performing Dijkstra's algorithm by maintaining a fibonacci heap
void extract_min_fibheap(vector<fibheap_node *> &heap, vector<fibheap_node *> &tree_roots, pair<long long int, long long int> &min_node_data, long long int n){

	fibheap_node *del_node = heap[0] ;
	fibheap_node *node_child = del_node->child ;
	min_node_data = make_pair(del_node->vertex,del_node->dist) ;
	if((del_node->right)->vertex == del_node->vertex){
		if(node_child == NULL){
			heap[0] = NULL ;
			del_node->left = NULL ;
			del_node->right = NULL ;
			delete del_node ;
			return ;
		}
	}
	if(node_child!=NULL){
		add_node_to_root_list(heap,tree_roots,node_child->vertex,0) ;
	}
	fibheap_node *node = del_node->right ;
	heap[0] = (heap[0])->left ;
	(heap[0])->right = node ;
	node->left = heap[0] ;
	del_node->left = NULL ;
	del_node->right = NULL ;
	heap[del_node->vertex] = NULL ;
	delete del_node ;
	tree_roots.resize(n+1,NULL) ;
	consolidate_heap(heap,tree_roots,n) ;

}


//Running Dijkstra's algorithm by maintaining an array of nodes of the graph, and running decrease_key and extract_min operations on them
void dijkstra_array(vector<edge> *graph, long long int dist_arr[], long long int n, long long int s){

	long long int arr[n][2], completed[n+1], indexes[n+1], j=1, last_index = n-1 ;
	arr[0][0]=s ;
	arr[0][1]=0 ;
	completed[0]=0 ;
	indexes[0]=-1 ;
	indexes[s]=0 ;
	for(long long int i=1 ; i<=n ; i++){
		if(i==s){
			completed[i] = 0 ;
			continue ;
		}
		else{
			completed[i] = 0 ;
			arr[j][0] = i ;
			arr[j][1] = 999999 ;
			indexes[i] = j ;
			j++ ;
		}
	}
	for(long long int i=1 ; i<=n ; i++){
		extract_min_array(arr,indexes,last_index) ;
		long long int u = arr[last_index][0], dist = arr[last_index][1] ;
		if(dist==999999){
			break ;
		}
		completed[u] = 1 ;
		last_index-- ;
		for(auto j=graph[u].begin() ; j!=graph[u].end() ; ++j){
			long long int v=j->first, w=j->second ;
			if((completed[v]==0) && (arr[indexes[u]][1] + w < arr[indexes[v]][1])){
				decrease_key_array(arr,indexes,indexes[v],arr[indexes[u]][1]+w) ;
			}
		}
	}
	for(long long int i=1 ; i<=n ; i++){
		if(i==1){
			if(arr[indexes[i]][1]==999999){
				cout << arr[indexes[i]][1] ;
				continue ;
			}
			cout << arr[indexes[i]][1] + dist_arr[i] - dist_arr[s] ;
		}
		else{
			if(arr[indexes[i]][1]==999999){
				cout << " " << arr[indexes[i]][1] ;
				continue ;
			}
			cout << " " << arr[indexes[i]][1] + dist_arr[i] - dist_arr[s] ;
		}
	}

}


//Running Dijkstra's algorithm by maintaining a binary heap of nodes of the graph, and running decrease_key and extract_min operations on them
void dijkstra_binary_heap(vector<edge> *graph, long long int dist_arr[], long long int n, long long int s){

	long long int arr[n][2], completed[n+1], indexes[n+1], j=1, last_index = n-1 ;
	arr[0][0]=s ;
	arr[0][1]=0 ;
	completed[0]=0 ;
	indexes[0]=-1 ;
	indexes[s]=0 ;
	for(long long int i=1 ; i<=n ; i++){
		if(i==s){
			completed[i] = 0 ;
			continue ;
		}
		else{
			completed[i] = 0 ;
			arr[j][0] = i ;
			arr[j][1] = 999999 ;
			indexes[i] = j ;
			j++ ;
		}
	}
	for(long long int i=1 ; i<=n ; i++){
		extract_min_binary_heap(arr,indexes,last_index) ;
		long long int u = arr[last_index][0], dist = arr[last_index][1] ;
		if(dist==999999){
			break ;
		}
		completed[u] = 1 ;
		last_index-- ;
		for(auto j=graph[u].begin() ; j!=graph[u].end() ; ++j){
			long long int v=j->first, w=j->second ;
			if((completed[v]==0) && (arr[indexes[u]][1] + w < arr[indexes[v]][1])){
				decrease_key_binary_heap(arr,indexes,indexes[v],arr[indexes[u]][1]+w) ;
			}
		}
	}
	for(long long int i=1 ; i<=n ; i++){
		if(i==1){
			if(arr[indexes[i]][1]==999999){
				cout << arr[indexes[i]][1] ;
				continue ;
			}
			cout << arr[indexes[i]][1] + dist_arr[i] - dist_arr[s] ;
		}
		else{
			if(arr[indexes[i]][1]==999999){
				cout << " " << arr[indexes[i]][1] ;
				continue ;
			}
			cout << " " << arr[indexes[i]][1] + dist_arr[i] - dist_arr[s] ;
		}
	}

}


//Running Dijkstra's algorithm by maintaining a binomial heap of nodes of the graph, and running decrease_key and extract_min operations on them
void dijkstra_binomial_heap(vector<edge> *graph, long long int dist_arr[], long long int n, long long int s){

	vector<binheap_node *> heap(n+1,NULL) ;
	long long int node_counter = 1 ;
	int bin_num[24], log_val=0, it=0 ;
	make_binary_number(bin_num,&log_val,n) ;
	vector<binheap_node *> tree_roots(log_val+1,NULL) ;
	construct_binheap(heap,tree_roots,&node_counter,bin_num,log_val,0) ;
	binheap_node *head = NULL ;
	while(tree_roots[it]==NULL){
		it++ ;
	}
	head = tree_roots[it] ;
	decrease_key_binomial_heap(heap,&head,s,0) ;
	long long int final_dist[n+1], completed[n+1] ;
	for(long long int i=0 ; i<=n ; i++){
		final_dist[i] = 0 ;
		completed[i] = 0 ;
	}
	for(long long int i=1 ; i<=n ; i++){
		pair<long long int, long long int> min_node_data ;
		extract_min_binomial_heap(heap,tree_roots,min_node_data,&head,log_val) ;
		long long int u=min_node_data.first, dist=min_node_data.second ;
		if(dist==999999){
			continue ;
		}
		completed[u] = 1 ;
		final_dist[u] = dist ;
		for(auto j=graph[u].begin() ; j!=graph[u].end() ; ++j){
			long long int v=j->first, w=j->second ;
			if((completed[v]==0) && (final_dist[u] + w  < (heap[v])->dist)){
				decrease_key_binomial_heap(heap,&head,v,final_dist[u]+w) ;
			}
		}
	}
	for(long long int i=1 ; i<=n ; i++){
		if(i==1){
			if(completed[i]==0){
				cout << "999999" ;
				continue ;
			}
			cout << final_dist[i] + dist_arr[i] - dist_arr[s] ;
		}
		else{
			if(completed[i]==0){
				cout << " " << "999999" ;
				continue ;
			}
			cout << " " << final_dist[i] + dist_arr[i] - dist_arr[s] ;
		}
	}

}


//Running Dijkstra's algorithm by maintaining a fibonacci heap of nodes of the graph, and running decrease_key and extract_min operations on them
void dijkstra_fibonacci_heap(vector<edge> *graph, long long int dist_arr[], long long int n, long long int s){

	vector<fibheap_node *> heap(n+1,NULL) ;
	long long int node_counter = 1 ;
	int bin_num[24], log_val=0, it=0 ;
	make_binary_number(bin_num,&log_val,n) ;
	vector<fibheap_node *> tree_roots(n+1,NULL) ;
	construct_fibheap_2(heap,tree_roots,&node_counter,bin_num,log_val,0) ;
	modify_fibheap(heap,tree_roots,bin_num,log_val) ;
	decrease_key_fibheap(heap,tree_roots,s,0) ;
	long long int final_dist[n+1], completed[n+1] ;
	for(long long int i=0 ; i<=n ; i++){
		final_dist[i] = 0 ;
		completed[i] = 0 ;
	}
	for(long long int i=1 ; i<=n ; i++){
		pair<long long int, long long int> min_node_data ;
		extract_min_fibheap(heap,tree_roots,min_node_data,n) ;
		long long int u=min_node_data.first, dist=min_node_data.second ;
		if(dist==999999){
			continue ;
		}
		completed[u] = 1 ;
		final_dist[u] = dist ;
		for(auto j=graph[u].begin() ; j!=graph[u].end() ; ++j){
			long long int v=j->first, w=j->second ;
			if((completed[v]==0) && (final_dist[u] + w  < (heap[v])->dist)){
				decrease_key_fibheap(heap,tree_roots,v,final_dist[u]+w) ;
			}
		}
	}
	for(long long int i=1 ; i<=n ; i++){
		if(i==1){
			if(completed[i]==0){
				cout << "999999" ;
				continue ;
			}
			cout << final_dist[i] + dist_arr[i] - dist_arr[s] ;
		}
		else{
			if(completed[i]==0){
				cout << " " << "999999" ;
				continue ;
			}
			cout << " " << final_dist[i] + dist_arr[i] - dist_arr[s] ;
		}
	}

}


//Performing Bellman Ford's algorithm on the initial graph with source as the dummy node with n edges all with weight 0 to all other nodes
//This is used to store the corresponding vertex wights in dist_array, to be used while reweighting the graph and further applying Dijkstra's algorithm
void bellman_ford(vector<edge> *graph, long long int dist_array[], long long int n, int d, int *neg_weight_cycle){

	dist_array[0]=-1 ;
	for(long long int i=1 ; i<=n+1 ; i++){
		if(i==n+1){
			dist_array[i]=0 ;
		}
		else{
			dist_array[i]=999999 ;
		}
	}
	for(long long int i=1 ; i<=n+1 ; i++){
		long long int relaxes_this_cycle=0 ;
		for(long long int u=1 ; u<=n+1 ; u++){
			if(dist_array[u]==999999){
					continue ;
				}
			for(auto k=graph[u].begin() ; k!=graph[u].end() ; ++k){
				long long int v=k->first, w=k->second ;
				if(dist_array[u] + w < dist_array[v]){
					dist_array[v]=dist_array[u]+w ;
					relaxes_this_cycle++ ;
				}
			}
		}
		if(relaxes_this_cycle==0){
			break ;
		}
		if(relaxes_this_cycle>0 && i==n+1){
			*neg_weight_cycle = 1 ;
			return ;
		}
	}

}


//Runs Johnson's algorithm by running Bellman Ford's algirthm, and further Dijkstra's algorithm n times
//The data structure used to perform Dijkstra's algorithm depends on the command line input (heap_type) given
void johnsons_algo(vector<edge> *graph, long long int n, int d, int heap_type, int *neg_weight_cycle){

	if((*neg_weight_cycle)==1){
		cout << "-1" ;
		return ;
	}
	long long int dist_array[n+2] ;
	for(long long int i=1 ; i<=n ; i++){
		graph[n+1].push_back(make_pair(i,0)) ;
	}
	bellman_ford(graph,dist_array,n,d,neg_weight_cycle) ;
	if((*neg_weight_cycle)==1){
		cout << "-1" ;
		return ;
	}
	vector<edge> *graph_new = new vector<edge>[n+1] ;
	reweight_graph(graph,graph_new,dist_array,n) ;
	for(long long int i=1 ; i<=n ; i++){
		if(heap_type==1){
			dijkstra_array(graph_new,dist_array,n,i) ;
		}
		else if(heap_type==2){
			dijkstra_binary_heap(graph_new,dist_array,n,i) ;
		}
		else if(heap_type==3){
			dijkstra_binomial_heap(graph_new,dist_array,n,i) ;
		}
		else if(heap_type==4){
			dijkstra_fibonacci_heap(graph_new,dist_array,n,i) ;
		}
		if(i!=n){
			cout << endl ;
		}
	}
	delete_weighted_graph(graph_new,n) ;

}


//Used to run a single test case (print the output of running Johnson's algorithm + storing the time taken it to run it)
void perform_ops(double time_array[], int heap_type, int i){

	long long int n ;
	int d, neg_weight_cycle = 0 ;
	cin >> n >> d ;
	clock_t start, end ;
	vector<edge> *graph = new vector<edge>[n+2] ;
	create_adjacency_weighted_list(graph,n,d,&neg_weight_cycle) ;
	start = clock() ;
	johnsons_algo(graph,n,d,heap_type,&neg_weight_cycle) ;
	end = clock() ;
	time_array[i] = double(end-start)/double(CLOCKS_PER_SEC) ;
	delete_weighted_graph(graph,n+1) ;

}


int main(int argc, char *argv[]){

	int t ;
	cin >> t ;
	double time_array[t] ;

	int heap_type = stoi(argv[1]) ;

	if((heap_type!=1 && heap_type!=2) && (heap_type!=3 && heap_type!=4)){
		cout << "Invalid Command Line Arguement" ;
	}

	else{
		for(int i=0 ; i<t ; i++){

			perform_ops(time_array,heap_type,i) ;
			cout << endl ;

		}

		for(int i=0 ; i<t ; i++){

			if(i==0){
				cout << time_array[i] ;
			}
			else{
				cout << " " << time_array[i] ;
			}

		}
	}

	return 0 ;

}