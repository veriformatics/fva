// T7 export wrapper: GLM 1.0.3's double specialization of glm::iround as a C-ABI function.
#include <glm/ext/scalar_common.hpp>

extern "C" int iround(double x) { return glm::iround(x); }
