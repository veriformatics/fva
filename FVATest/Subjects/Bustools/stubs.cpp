// Count-only build: the other command entry points of bustools_main abort (never reached by fromtext/count).
#include <cstdlib>
#include "Common.hpp"
#include "BUSData.h"
#include "bustools_capture.h"
#include "bustools_clusterhist.h"
#include "bustools_collapse.h"
#include "bustools_compress.h"
#include "bustools_correct.h"
#include "bustools_decompress.h"
#include "bustools_extract.h"
#include "bustools_inspect.h"
#include "bustools_linker.h"
#include "bustools_mash.h"
#include "bustools_merge.h"
#include "bustools_predict.h"
#include "bustools_project.h"
#include "bustools_sort.h"
#include "bustools_umicorrect.h"
#include "bustools_whitelist.h"
void bustools_capture(Bustools_opt &opt) { std::abort(); }
void bustools_clusterhist(Bustools_opt &opt) { std::abort(); }
void bustools_collapse(Bustools_opt &opt) { std::abort(); }
void bustools_compress(const Bustools_opt &opt) { std::abort(); }
void bustools_split_correct(Bustools_opt &opt) { std::abort(); }
void bustools_correct(Bustools_opt &opt) { std::abort(); }
void bustools_decompress(const Bustools_opt &opt) { std::abort(); }
void bustools_extract(const Bustools_opt& opt) { std::abort(); }
void bustools_inspect(Bustools_opt &opt) { std::abort(); }
void bustools_linker(Bustools_opt &opt) { std::abort(); }
void bustools_mash(const Bustools_opt &opt) { std::abort(); }
void bustools_merge_different_index(const Bustools_opt &opt) { std::abort(); }
void bustools_predict(Bustools_opt &opt) { std::abort(); }
void bustools_project(Bustools_opt &opt) { std::abort(); }
void bustools_sort_orig(const Bustools_opt& opt) { std::abort(); }
void bustools_sort(const Bustools_opt& opt) { std::abort(); }
void bustools_umicorrect(const Bustools_opt& opt) { std::abort(); }
void bustools_whitelist(Bustools_opt &opt) { std::abort(); }
