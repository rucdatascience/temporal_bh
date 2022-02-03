# Hunting Temporal Bumps in Graphs with Dynamic Vertex Properties

These fils are for our paper:

Yahui Sun, Shuai Ma, and Bin Cui. “Hunting temporal bumps in graphs with dynamic vertex properties.” Proceedings of the 2022 ACM SIGMOD international conference on management of data (2022)


The introduction of these files are as follows. 


# Datasets

<b>The New York dataset</b> is in the NY folder. The dictionary is as follows.

intersections_num = 77580 roads_num = 119228

The columns of "NY_road_network_intersections.txt" are "Intersection ID lon lat". For example, 
"Intersection 0 -73.8786154402 40.8619153015" means that the location (lon lat) of Intersection 0 
is "-73.8786154402 40.8619153015".

The columns of "NY_road_network_roads.txt" are "Road Intersection_ID_1 Intersection_ID_2 Distance".
For example, "Road 70271 70272 0.0759936942947" means that the road between intersection 70271
and intersection 70272 is 0.0759936942947 km.

The columns of "NY_taxi_trip_2015_1_x.txt" are "start_year,start_month,start_day,start_hour(0-23),start_minute(0-59),
start_intersection,end_year,end_month,end_day,end_hour(0-23),end_minute(0-59),end_intersection". For example, 
"2015,1,1,19,5,14217,2015,1,1,19,23,5095" means that there is a trip starting from intersection 14217
at 2015-1-1 19:5, and ending at intersection 5095 at 2015-1-1 19:23.



<b>The Reddit dataset</b> is in the Reddit folder. The dictionary is as follows.

Community_num = 148873, Keyword_num = 591072, community_keyword_pair_num (dummy_vertex_num) = 1023334

In "Communities.txt", an example line content is "r/phinvest	1000035", 
which means that the ID of community "r/phinvest" is 1000035.

In "Keywords.txt", an example line content is "personal space	2", 
which means that the ID of keyword "personal space" is 2.

In "dummy_vertex_IDs.txt", an example line content is "1008668+287955	2247821", 
which means that the pair of community 1008668 and keyword 287955 has an ID of 2247821.


Each comment file, e.g., "Comments_2019_9_1.txt",  records the comment data for a day.
An example line content in a comment file is "2604152	6_2,7_5", 
which means that the details of comments corresponding to dummy vertex 2604152 (suppose that 2604152 corresponds to 
the pair of community X and keyword Y; then these comments are in community X and contain keyword Y) is 6_2,7_5,
i.e., there are 2 comments in hour 6 and 5 comments in hour 7 (the hour ID is from 0 to 23).




<b>The Wikipedia dataset</b> is in the Wiki_1M folder. The dictionary is as follows.

page_num = 1176192 page_connection_num = 11124449

In "Wiki_pages_1176k_undirected.txt", an example line content is "0 Lily_Laita", 
which means that the name of page 0 is Lily_Laita.

In "Wiki_pagerelationships_1176k_undirected.txt", an example line content is "422690 1158259", 
which means that page 422690 is linked to page 1158259.

Each pageview file, e.g., "pageviews_1176k_2020_1_1.txt",  records the pageview data for a day.
An example line content in a page view file is "607329 2 F1W1", 
which means that the total pageview of page 607329 in this day is 2, and the detail of this pageview is F1W1, and 
<Hour: from 0 to 23, written as 0 = A, 1 = B ... 22 = W, 23 = X>, i.e., F1W1 means that there is 1 pageview in hour F
and 1 pageview in hour W



# C++ codes 

The C++ source codes are in <b>TBH.cpp</b>. 

It is recommended to fold all the regions of codes for easy reading (by pressing Ctrl+M+O in Visual Studio). 

Running these codes requires some header files (e.g. #include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted.h>; see cppheader.zip) and the Boost library: https://www.boost.org/ (e.g. #include <boost/random.hpp>) . 

After making the header files ready, some <b>Example Experiments</b> can be conducted by running the function "example_experiments()", we have provided some comments/instructions inside this function. All the experiments in our paper can be produced in the same way as "example_experiments()".

To read these C++ codes in detail, it is recommended to start from "example_experiments()", and then go to "experiment_element". More detailed codes in other regions can then be traced. There are some directions on these codes as follows. 

1) The codes of our MIRROR and S-MIRROR algorithms are below "/*accelerated_MIRROR and accelerated_S_MIRROR*/"
2) The codes of our H-MIRROR and H-S-MIRROR algorithms are below "/*accelerated_H_MIRROR and accelerated_H_S_MIRROR*/"
3) The codes of baseline algorithms are below "/*adapted static algorithms for hunting temporal bumps*/"

