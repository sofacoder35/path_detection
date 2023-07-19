#include <iostream>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <thread>
#include <chrono>
#include "fstream"
#include "algorithm"
#include "mutex"
#include "math.h"
#include "on_the_fly_scc_union_find.hpp"
#include "on_the_fly_scc_graph_node.h"
#include "simple_storage.h"

#include "windows.h"
#include "process.h"
#include "psapi.h"
#include "parallel_tarjan_algorithm.h"
#include "sequential_set_based_algorithm.h"
#include "multi_core_on_the_fly_scc_decomposition_algorithm.h"


using namespace std;
//using namespace parallel_union_find::union_find::blocking;
//using namespace parallel_union_find::graph_node;
//using namespace parallel_union_find::algorithm;
//using namespace parallel_union_find::storage;

string file_name="iceland.txt";
int start_node_num=1,target_node_num=45;
const int    threads = 2;
int vertex_numbers=20;
int edge_numbers=100;



mutex mtx;
pthread_spinlock_t spinlock;

using node = on_the_fly_scc_graph_node<on_the_fly_scc_union_find>;

std::unordered_map<size_t, size_t> input_to_idx;
simple_storage<node> storage;

void showMemoryInfo() {
    PROCESS_MEMORY_COUNTERS pmc;
    GetProcessMemoryInfo(GetCurrentProcess(), &pmc, sizeof(pmc));
    SIZE_T virtualMemUsedByMe = pmc.WorkingSetSize;
    SIZE_T pagefileMemUsedByMe = pmc.PagefileUsage;
    cout << "Memory used: " << (virtualMemUsedByMe) / 1024.0 / 1024.0 << " MB" << endl;

}

void get_input()
{
    size_t from, to;
    size_t read_lines = 0;

    int i=0;
    while (i< 1000)
    {
        from=rand()%1000000+1;
        to=rand()%1000000+1;
        int j=0;
        for (size_t x : {from, to})
            if (input_to_idx.find(x) == input_to_idx.end())
            {
                input_to_idx.emplace(x, input_to_idx.size());

                // make sure we have enough space
                if (storage.capacity() <= input_to_idx.at(x))
                    storage.resize(input_to_idx.at(x) + 1);

                // create node
                new (storage.at(input_to_idx.at(x))) node();

                // give it label from input
                storage.at(input_to_idx.at(x))->set_label(x);
            }

        // add edge from -> to
        storage.at(input_to_idx.at(from))->add_son(storage.at(input_to_idx.at(to)));
        i++;
        // print progress
//        if (++read_lines % 5000000 == 0)
//            cerr << "Read " << read_lines / 1000000 << "M rows" << endl;
    }
}

void get_input_from_file(){

    fstream fp;
    fp.open("E:/OneDrive/OneDrive - stu.hqu.edu.cn/parallel_union_find_win/data/"+file_name,std::ios::in);
    int from,to;
    while (fp >> from >> to)
    {
        for (size_t x : {from, to})
            if (input_to_idx.find(x) == input_to_idx.end())
            {
                input_to_idx.emplace(x, input_to_idx.size());

                // make sure we have enough space
                if (storage.capacity() <= input_to_idx.at(x))
                    storage.resize(input_to_idx.at(x) + 1);

                // create node
                new (storage.at(input_to_idx.at(x))) node();

                // give it label from input
                storage.at(input_to_idx.at(x))->set_label(x);
            }

        // add edge from -> to
        storage.at(input_to_idx.at(from))->add_son(storage.at(input_to_idx.at(to)));


    }
    cout<<"input over"<<endl;
}
size_t get_first_unused_id()
{

    size_t candidate = 0;

    // first unused id
    while (input_to_idx.find(candidate) != input_to_idx.end())
        ++candidate;

    input_to_idx.emplace(candidate, input_to_idx.size());

    // create node for that id
    if (storage.size() <= input_to_idx.at(candidate))
        storage.resize(input_to_idx.at(candidate) + 1);
    new (storage.at(input_to_idx.at(candidate))) node();

    // connect it to all other nodes, even itself (it does not change anything)
    for (size_t i = 0; i < storage.size(); ++i)
        storage.at(input_to_idx.at(candidate))->add_son(storage.at(i));

    return candidate;


}
void get_input_random(){
    srand(time(0)+rand());
    size_t i=0;
    while(i<edge_numbers){
        int from=rand()%vertex_numbers+1;
        int to=rand()%vertex_numbers+1;
        for (size_t x : {from, to})
            if (input_to_idx.find(x) == input_to_idx.end()){

                input_to_idx.emplace(x, input_to_idx.size());

                // make sure we have enough space
                if (storage.capacity() <= input_to_idx.at(x))
                    storage.resize(input_to_idx.at(x) + 1);

                // create node
                new (storage.at(input_to_idx.at(x))) node();

                // give it label from input
                storage.at(input_to_idx.at(x))->set_label(x);
            }

        // add edge from -> to
        storage.at(input_to_idx.at(from))->add_son(storage.at(input_to_idx.at(to)));


        i++;
    }

}

bool check_alg(const string& str)
{
    if (str == "TARJAN")
        return true;
    else if (str == "SET_BASED")
        return true;
    else if (str == "ON_THE_FLY")
        return true;
    else
        return false;
}


void dfs_parallel_v1(node *start_node,node *target_node){
    srand(time(0)+rand());
    using GNiterator = typename node::iterator;

    std::unordered_map<node*, bool>               current_path_nodes;
    std::stack<node*>                             stack_explore_nodes_v; // nodes v
    std::stack<std::pair<GNiterator, GNiterator>>    stack_explore_iterators; // iterators to neighbors of stack_explore_nodes_vp

    stack_explore_nodes_v.emplace(storage.at(input_to_idx.at(-1)));

    stack_explore_iterators.emplace(storage.at(input_to_idx.at(-1))->get_random_neighbors_iterators());
    storage.at(input_to_idx.at(-2))->mark_as_reachable();

    target_node->mark_as_reachable();
    target_node->mark_as_completed();

    node *v,*u;

    while (!stack_explore_nodes_v.empty()){
        v=stack_explore_nodes_v.top();
//        cout<<v->_label<<endl;
            if(stack_explore_iterators.top().first == stack_explore_iterators.top().second){
                for (int i = 0; i < v->_neighbors.size(); ++i) {
                    if(v->_neighbors[i]->is_reachable()){
                        for (int j = 0; j < v->find_set()->_scc_nodes.size(); ++j) {
                            v->find_set()->_scc_nodes[j]->mark_as_reachable();
                        }
                        break;
                    }
                }
                current_path_nodes.erase(stack_explore_nodes_v.top());
                stack_explore_nodes_v.pop();
                stack_explore_iterators.pop();
                
            }
            else{
                u=*stack_explore_iterators.top().first;
                ++stack_explore_iterators.top().first;
                if(current_path_nodes.find(u)==current_path_nodes.end()){
                    current_path_nodes.emplace(u,true);
                    stack_explore_nodes_v.emplace(u);
                    stack_explore_iterators.emplace(u->get_random_neighbors_iterators());
                }
            }
    }
}
void dfs_parallel_v3(node *start_node,node *target_node){
    srand(time(0)+rand());
    using GNiterator = typename node::iterator;

    std::unordered_map<node*, bool>               current_path_nodes;
    std::stack<node*>                             stack_explore_nodes_v; // nodes v
    std::stack<std::pair<GNiterator, GNiterator>>    stack_explore_iterators; // iterators to neighbors of stack_explore_nodes_vp

    stack_explore_nodes_v.emplace(storage.at(input_to_idx.at(-1)));

    stack_explore_iterators.emplace(storage.at(input_to_idx.at(-1))->get_random_scc_neighbors_iterators());
    storage.at(input_to_idx.at(-2))->mark_as_reachable();


    node *v,*u;

    while (!stack_explore_nodes_v.empty()){
        v=stack_explore_nodes_v.top();
        cout<<v->_label<<endl;
            if(stack_explore_iterators.top().first == stack_explore_iterators.top().second){
                for (int i = 0; i < v->_neighbors.size(); ++i) {
                    if(v->_neighbors[i]->is_reachable()){
                        for (int j = 0; j < v->find_set()->_scc_nodes.size(); ++j) {
                            v->find_set()->_scc_nodes[j]->mark_as_reachable();
                        }
                        break;
                    }
                }
                current_path_nodes.erase(stack_explore_nodes_v.top());
                stack_explore_nodes_v.pop();
                stack_explore_iterators.pop();

            }
            else{
                u=*stack_explore_iterators.top().first;
                ++stack_explore_iterators.top().first;
                if(current_path_nodes.find(u)==current_path_nodes.end()){
                    current_path_nodes.emplace(u,true);
                    stack_explore_nodes_v.emplace(u);
                    stack_explore_iterators.emplace(u->get_random_scc_neighbors_iterators());
                }
            }
    }
}

void preprocess(node *start_node,node *target_node){
    input_to_idx.emplace(-1,input_to_idx.size());
    input_to_idx.emplace(-2,input_to_idx.size());

    // create node for that id
    if (storage.size() <= input_to_idx.size())
        storage.resize(input_to_idx.size() + 2);

    new (storage.at(input_to_idx.at(-1))) node();
    new (storage.at(input_to_idx.at(-2))) node();

    storage.at(input_to_idx.at(-1))->set_label(-1);
    storage.at(input_to_idx.at(-2))->set_label(-2);

    storage.at(input_to_idx.at(-1))->add_son(start_node);
    target_node->add_son(storage.at(input_to_idx.at(-2)));
}

void calc_scc_edge(node *node){
    for (int i = 0; i < node->_scc_nodes.size(); ++i) {
        for (int j = 0; j < node->_scc_nodes[i]->_neighbors.size(); ++j) {
            if (node->_scc_nodes[i]->_neighbors[j]->find_set() != node &&
            find(node->_neighbor_representative_nodes.begin(),node->_neighbor_representative_nodes.end(),
                 node->_scc_nodes[i]->_neighbors[j]->find_set())==node->_neighbor_representative_nodes.end()){
                node->_neighbor_representative_nodes.push_back(node->_scc_nodes[i]->_neighbors[j]->find_set());
            }
        }
    }
}

void dfs_parallel_v2(node *start_node,node *target_node){
    srand(time(0)+rand());

    using GNiterator = typename node::iterator;

    std::stack<node*>                             stack_explore_nodes_v; // nodes v
    std::stack<std::pair<GNiterator, GNiterator>>    stack_explore_iterators; // iterators to neighbors of stack_explore_nodes_vp

    stack_explore_nodes_v.emplace(storage.at(input_to_idx.at(-1)));

    stack_explore_iterators.emplace(storage.at(input_to_idx.at(-1))->get_random_scc_neighbors_iterators());

    storage.at(input_to_idx.at(-2))->mark_as_reachable();
    storage.at(input_to_idx.at(-2))->mark_as_completed();

    node *v,*u;

    while (!stack_explore_nodes_v.empty()){
        v=stack_explore_nodes_v.top();
//        cout<<v->get_label()<<endl;
        if(v->is_completed()){
            stack_explore_nodes_v.pop();
            stack_explore_iterators.pop();
        }
        else{
            if(stack_explore_iterators.top().first == stack_explore_iterators.top().second){
                v->mark_as_completed();
                for (int i = 0; i < v->_neighbor_representative_nodes.size(); ++i) {
                    if(v->_neighbor_representative_nodes[i]->is_reachable()){
                        for (int j = 0; j < v->_scc_nodes.size(); ++j) {
                            v->_scc_nodes[j]->mark_as_reachable();
                        }
                        break;
                    }
                }

                stack_explore_nodes_v.pop();
                stack_explore_iterators.pop();

            }
            else{
                u=*stack_explore_iterators.top().first;
                ++stack_explore_iterators.top().first;

                    stack_explore_nodes_v.emplace(u);
                    stack_explore_iterators.emplace(u->get_random_scc_neighbors_iterators());



            }
        }


    }
}

void async_task(int begin,int end){
    for (int i = begin; i < end; ++i) {
        if(storage.at(i)->_scc_nodes.size()<1)
            continue;
        for (int j = 0; j < storage.at(i)->_scc_nodes.size(); ++j) {
            for (int k = 0; k < storage.at(i)->_scc_nodes[j]->_neighbors.size(); ++k) {
                if (storage.at(i)->_scc_nodes[j]->_neighbors[k]->find_set()!=storage.at(i)
                    && find(storage.at(i)->_neighbor_representative_nodes.begin(),
                            storage.at(i)->_neighbor_representative_nodes.end(),
                            storage.at(i)->_scc_nodes[j]->_neighbors[k]->find_set())
                       ==storage.at(i)->_neighbor_representative_nodes.end())
                    storage.at(i)->_neighbor_representative_nodes.push_back(storage.at(i)->_scc_nodes[j]->_neighbors[k]->find_set());
            }
        }

    }
    cout<<"async task finished"<<endl;
}

int main(int argc, char* argv[])
{
    // help
//    if (argc == 2 && string(argv[1]) == "--help")
//    {
//
//        cout << "usage: ./test_pokec_simple ALG N < input.txt > ouput.txt\n";
//        cout << "ALG - algorithm, <TARJAN, SET_BASED, ON_THE_FLY>\n";
//        cout << "N - number of threads\n";
//
//        cout << "input format from stdin:\n";
//        cout << "each line: number(n1) <delimiter(space, tab)> number(n2)\n";
//        cout << "explanation: each line means ordered edge from n1 to n2\n";
//        return 0;
//    }
    setbuf(stdout, 0);
    // read input
    const string alg = "ON_THE_FLY";

    size_t       start_node_id;


    if (!check_alg(alg))
    {
        cout << "Don't know " << alg << " algorithm. Use --help option." << endl;
        return 0;
    }

//    get_input();
    get_input_from_file();
//    get_input_random();

    start_node_id = get_first_unused_id();

    // run algorithm
    auto time_scc_start = chrono::high_resolution_clock::now();


    if (alg == "TARJAN")
    {
        vector<thread> vec_threads;
        node* start_node = storage.at(input_to_idx.at(start_node_id));

        for (int i = 0; i < threads; ++i)
            vec_threads.emplace_back(parallel_tarjan_algorithm<node>, start_node, (1 << i));

        for (int i = 0; i < threads; ++i)
            vec_threads.at(i).join();
    }
    else if (alg == "SET_BASED")
    {
        vector<thread> vec_threads;
        node* start_node = storage.at(input_to_idx.at(start_node_id));

        for (int i = 0; i < threads; ++i)
            vec_threads.emplace_back(sequential_set_based_algorithm<node>, start_node, (1 << i));

        for (int i = 0; i < threads; ++i)
            vec_threads.at(i).join();
    }
    else if (alg == "ON_THE_FLY")
    {

        vector<thread> vec_threads;
        node* start_node = storage.at(input_to_idx.at(start_node_id));

        for (int i = 0; i < threads; ++i)
            vec_threads.emplace_back(multi_core_on_the_fly_scc_decomposition_algorithm<node>, start_node, (1 << i));

        for (int i = 0; i < threads; ++i)
            vec_threads.at(i).join();
    }

    auto time_scc_finish = chrono::high_resolution_clock::now();

    // report information
    cout << "Algorithm scc finished in " << chrono::duration<double>(time_scc_finish - time_scc_start).count() << " seconds" << endl;

    node * start_node=storage.at(input_to_idx.at(start_node_num));
    node * target_node=storage.at(input_to_idx.at(target_node_num));

    preprocess(start_node,target_node);

    // number of SCCs
    unordered_set<node*> tops;
    for (int j=0;j<input_to_idx.size();j++) {
        if (j==input_to_idx.size()-3)continue;
        tops.emplace(storage.at(j)->find_set());
        storage.at(j)->find_set()->add_scc_node(storage.at(j));
//        for (int i = 0; i < storage.at(j)->_neighbors.size(); ++i) {
//            if(storage.at(j)->_neighbors[i]->find_set()!=storage.at(j)->find_set()
//            && find(storage.at(j)->find_set()->_neighbor_representative_nodes.begin(),
//                    storage.at(j)->find_set()->_neighbor_representative_nodes.end(),
//                    storage.at(j)->_neighbors[i]->find_set()) ==
//                    storage.at(j)->find_set()->_neighbor_representative_nodes.end() )
//            storage.at(j)->find_set()->_neighbor_representative_nodes.push_back(storage.at(j)->_neighbors[i]->find_set());
//        }
//        if(j%10000==0)
//        cout<<j<<endl;
    }
    int count=0;

    int interval=ceil((double)input_to_idx.size()/(double)threads);
    vector<thread> vec_threads;
    for (int i = 0; i < threads; ++i) {
        if(i==threads-1)
            vec_threads.emplace_back(async_task,  i*interval, input_to_idx.size());
        else
            vec_threads.emplace_back(async_task,   i*interval, (i+1)*interval);
    }
    for (int i = 0; i < threads; ++i)
        vec_threads.at(i).join();


    auto time_DAG_finish = chrono::high_resolution_clock::now();

    // report information
    cout << "Algorithm DAG finished in " << chrono::duration<double>(time_DAG_finish - time_scc_finish).count() << " seconds" << endl;

//    for (int i = 0; i < input_to_idx.size(); ++i) {
//        if(storage.at(i)->_scc_nodes.size()<1)
//            continue;
//        for (int j = 0; j < storage.at(i)->_scc_nodes.size(); ++j) {
//            for (int k = 0; k < storage.at(i)->_scc_nodes[j]->_neighbors.size(); ++k) {
//                if (storage.at(i)->_scc_nodes[j]->_neighbors[k]->find_set()!=storage.at(i)
//                && find(storage.at(i)->_neighbor_representative_nodes.begin(),
//                        storage.at(i)->_neighbor_representative_nodes.end(),
//                        storage.at(i)->_scc_nodes[j]->_neighbors[k]->find_set())
//                        ==storage.at(i)->_neighbor_representative_nodes.end())
//                    storage.at(i)->_neighbor_representative_nodes.push_back(storage.at(i)->_scc_nodes[j]->_neighbors[k]->find_set());
//            }
//        }
//
//    }



//    for (int i = 0; i < input_to_idx.size(); ++i) {
//        cout<<storage.at(i)->get_label()<<" : ";
//        for (int j = 0; j < storage.at(i)->_scc_nodes.size(); ++j) {
//            cout<<storage.at(i)->_scc_nodes[j]->get_label()<<' ';
//        }
//        cout<<endl;
//    }
//    cout<<endl;
//    for (int i = 0; i < input_to_idx.size(); ++i) {
//        cout<<storage.at(i)->get_label()<<" : ";
//        for (int j = 0; j < storage.at(i)->_neighbor_representative_nodes.size(); ++j) {
//            cout<<storage.at(i)->_neighbor_representative_nodes[j]->get_label()<<' ';
//        }
//        cout<<endl;
//    }

    vector<thread> vec_threads1;
//
    for (int i = 0; i < threads; ++i)
        vec_threads1.emplace_back(dfs_parallel_v2,start_node,target_node);

    for (int i = 0; i < threads; ++i)
        vec_threads1.at(i).join();

//    dfs_parallel_v1(start_node,target_node);


//    dfs_parallel_v1(start_node,target_node);

    int cnt=0;

    for (int i = 0; i < input_to_idx.size()-3; ++i) {
        if(storage.at(i)->is_reachable()){
            cnt++;
        }
    }
    cerr<<"reachable cnt : "<< cnt << endl;

    cerr<<"total cnt : "<< tops.size() << endl;

    auto time_finish_parallel = chrono::high_resolution_clock::now();
    // report information
    cout << "Algorithm finished in " << chrono::duration<double>(time_finish_parallel - time_DAG_finish).count() << " seconds" << endl;
    showMemoryInfo();

//    cerr << "Number of components is " << tops.size() << endl;
}

