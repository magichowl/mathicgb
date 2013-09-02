// MathicGB copyright 2012 all rights reserved. MathicGB comes with ABSOLUTELY
// NO WARRANTY and is licensed as GPL v2.0 or later - see LICENSE.txt.
#include "mathicgb/stdinc.h"

#include "mathicgb/Poly.hpp"
#include "mathicgb/Basis.hpp"
#include "mathicgb/ModuleMonoSet.hpp"
#include "mathicgb/io-util.hpp"
#include "mathicgb/PolyHeap.hpp"
#include "mathicgb/SigPolyBasis.hpp"
#include "mathicgb/SignatureGB.hpp"
#include "mathicgb/ClassicGBAlg.hpp"
#include "mathicgb/mtbb.hpp"
#include "mathicgb/MathicIO.hpp"
#include "mathicgb/Scanner.hpp"
#include "test/ideals.hpp"
#include <cstdio>
#include <string>
#include <iostream>
#include <sstream>
#include <memory>
#include <gtest/gtest.h>

using namespace mgb;

TEST(IO, ideal) {
  const char* idealA_fromStr_format = 
"32003 6 \
1 1 1 1 1 1 1 \
3 \
-bc+ad \
-b2+af \
-bc2+a2e \
";

  std::unique_ptr<Basis> I = basisParseFromString(idealA_fromStr_format);
  EXPECT_EQ("  -bc+ad\n  -b2+af\n  -bc2+a2e\n", toString(I.get()));
}

void testNoUsefulSPoly(std::unique_ptr<Reducer> reducer, const PolyBasis& pbasis){
  size_t sz = pbasis.size();
  for (size_t i = 0; i != sz; ++i)
    for (size_t j = i+1; j != sz; ++j)            
      ASSERT_TRUE(reducer->classicReduceSPoly(pbasis.poly(i),
                                              pbasis.poly(j), pbasis)->isZero())
                       <<"the computed polybasis is not a Grobner basis!";
}

void testGB(
  std::string idealStr,
  std::string sigBasisStr,
  std::string syzygiesStr,
  std::string initialIdealStr,
  size_t nonSingularReductions
) {
  // Put the contents of pict.out into allPairsTest as a string. This
  // works because pict.out does not have any commas and we do not
  // care about whitespace. pict.out contains a set of tests such that
  // all pairs of parameters are covered by at least one test. See
  // pict.in for details.
#define MATHICGB_ESCAPE_MULTILINE_STRING(str) #str
char const allPairsTests[] = MATHICGB_ESCAPE_MULTILINE_STRING(
spairQueue	reducerType	divLookup	monTable	buchberger	postponeKoszul	useBaseDivisors	autoTailReduce	autoTopReduce	preferSparseReducers	useSingularCriterionEarly	sPairGroupType	threadCount
1	5	3	1	siggb	0	0	0	0	0	0	b	2
0	11	4	4	siggb	1	1	0	0	1	1	s	1
2	25	2	2	siggb	0	0	0	0	1	1	b	8
3	22	1	3	gb	0	0	1	1	1	0	s	2
0	3	4	1	gb	0	0	1	1	0	0	b	1
1	8	1	3	siggb	1	1	0	0	0	1	s	8
2	14	2	4	gb	0	0	1	1	0	0	b	8
3	1	3	2	siggb	1	1	0	0	1	1	s	1
3	5	2	1	siggb	1	1	0	0	1	1	b	8
1	16	3	3	gb	0	0	0	1	0	0	b	1
2	0	2	4	siggb	1	1	0	0	0	1	s	2
2	7	1	1	gb	0	0	1	0	0	0	s	1
1	8	4	1	gb	0	0	1	1	1	0	b	2
1	22	4	2	siggb	0	1	0	0	0	1	b	8
0	5	1	2	gb	0	0	1	1	1	0	s	1
2	3	3	3	siggb	1	1	0	0	1	1	s	8
0	10	3	1	gb	0	0	1	0	0	0	b	2
2	23	2	3	gb	0	0	1	1	0	0	b	1
1	1	1	4	gb	0	0	1	1	0	0	b	2
1	26	2	2	gb	0	0	1	0	0	0	s	2
0	7	4	2	siggb	1	1	0	0	1	1	b	8
3	12	4	2	gb	0	0	1	0	0	0	s	8
1	6	3	4	gb	0	0	1	0	1	0	b	8
0	6	2	1	siggb	1	1	0	0	0	1	s	2
2	20	4	2	gb	0	0	1	1	1	0	s	8
3	15	2	4	gb	0	0	1	0	0	0	s	8
0	2	4	3	gb	0	0	0	1	0	0	s	8
3	17	2	1	siggb	1	1	0	0	1	0	s	8
1	24	1	1	siggb	1	0	0	0	0	0	b	8
1	4	2	1	siggb	0	0	0	0	1	1	s	8
1	15	1	3	siggb	1	1	0	0	1	1	b	2
2	9	1	3	gb	0	0	1	0	1	0	s	2
3	24	2	3	siggb	0	1	0	0	1	1	s	2
0	21	1	1	siggb	0	1	0	0	1	1	b	8
2	24	3	4	siggb	1	1	0	0	0	1	b	1
0	23	1	2	siggb	1	1	0	0	1	1	s	8
2	12	3	3	siggb	1	1	0	0	1	1	b	2
0	20	3	1	siggb	1	1	0	0	0	1	b	2
0	15	3	2	siggb	0	1	0	0	0	1	b	1
3	23	3	1	siggb	0	0	0	0	0	1	s	2
2	8	2	2	gb	0	0	0	1	0	0	s	1
2	13	3	3	siggb	1	0	0	0	1	1	b	2
1	11	1	2	gb	0	0	1	1	0	0	b	8
0	18	3	1	siggb	0	1	0	0	0	1	s	8
2	5	4	3	siggb	1	0	0	0	0	1	b	2
1	23	4	4	siggb	0	1	0	0	1	1	b	2
2	19	2	2	gb	0	0	0	0	0	0	s	8
0	14	3	3	siggb	1	1	0	0	1	1	s	2
0	12	2	4	gb	0	0	0	1	1	0	s	1
2	10	2	2	siggb	1	1	0	0	1	1	s	1
3	13	2	2	gb	0	0	1	1	0	0	s	1
0	26	4	4	siggb	1	1	0	0	1	1	b	1
2	18	4	2	gb	0	0	1	1	1	0	b	1
3	11	2	1	siggb	1	1	0	0	1	1	s	2
1	0	1	3	gb	0	0	1	1	1	0	b	1
0	24	4	2	siggb	1	0	0	0	0	1	b	2
3	14	4	2	gb	0	0	0	0	1	0	s	1
0	22	3	4	gb	0	0	1	0	0	0	b	1
1	20	2	4	siggb	1	1	0	0	0	1	s	1
3	6	4	3	siggb	0	1	0	0	0	1	b	1
0	19	3	3	siggb	1	1	0	0	1	1	b	2
3	26	1	3	gb	0	0	0	1	1	0	b	8
2	26	3	1	siggb	0	1	0	0	1	0	b	2
1	25	4	3	gb	0	0	1	1	0	0	s	2
1	19	1	4	gb	0	0	1	1	0	0	s	1
2	15	4	1	siggb	1	0	0	0	0	1	s	8
3	4	1	4	gb	0	0	1	1	0	0	b	1
3	5	1	4	siggb	0	1	0	0	1	1	s	2
0	17	1	3	siggb	0	0	0	0	0	1	b	1
2	16	1	2	siggb	1	1	0	0	1	1	s	8
1	3	1	4	gb	0	0	1	1	0	0	b	2
1	9	2	4	siggb	1	1	0	0	0	1	b	8
1	7	3	3	siggb	0	0	0	0	0	1	b	2
1	18	2	4	gb	0	0	0	1	0	0	b	2
2	2	2	2	siggb	1	1	0	0	1	1	b	2
3	21	4	2	gb	0	0	1	1	0	0	s	1
3	10	1	3	siggb	0	0	0	0	0	1	s	8
2	1	2	1	siggb	1	1	0	0	0	1	b	8
0	4	4	3	gb	0	0	0	1	0	0	b	2
3	3	2	2	siggb	1	1	0	0	0	1	s	1
0	9	4	2	siggb	0	0	0	0	0	1	b	1
3	16	2	1	siggb	0	0	0	0	1	1	b	2
0	16	4	4	gb	0	0	1	0	1	0	b	1
3	18	1	3	gb	0	0	1	1	0	0	s	2
1	2	3	4	gb	0	0	1	0	0	0	b	1
1	13	1	4	gb	0	0	1	1	0	0	s	8
2	21	3	3	siggb	1	0	0	0	1	1	s	2
2	6	1	2	gb	0	0	1	1	1	0	s	2
3	19	4	1	gb	0	0	1	0	1	0	s	8
2	17	3	2	gb	0	0	1	1	0	0	s	2
2	11	3	3	siggb	0	1	0	0	1	1	s	8
0	8	3	4	gb	0	0	0	1	1	0	s	8
3	20	1	3	gb	0	0	0	1	1	0	s	1
1	21	2	4	gb	0	0	1	1	0	0	b	8
0	1	4	3	gb	0	0	1	0	1	0	s	2
3	9	3	1	gb	0	0	1	1	0	0	b	8
3	8	3	1	siggb	1	1	0	0	0	1	b	1
1	17	4	4	siggb	1	1	0	0	0	1	b	2
3	7	2	4	gb	0	0	1	1	0	0	s	2
1	14	1	1	siggb	1	0	0	0	1	0	b	8
0	13	4	1	siggb	0	1	0	0	0	1	s	2
1	12	1	1	siggb	1	0	0	0	0	1	s	8
0	0	4	1	siggb	0	0	0	0	0	1	b	8
2	4	3	2	gb	0	0	0	1	0	0	b	2
2	22	2	1	siggb	1	0	0	0	0	1	b	1
0	25	3	4	gb	0	0	1	0	1	0	s	1
3	25	1	1	gb	0	0	1	0	1	0	s	2
3	2	1	1	gb	0	0	0	1	1	0	b	8
0	24	1	4	gb	0	0	1	1	0	0	b	2
2	25	1	2	siggb	1	1	0	0	1	1	s	2
1	10	4	4	siggb	1	1	0	0	0	1	s	8
2	10	2	4	gb	0	0	1	1	0	0	s	8
2	18	2	1	siggb	1	1	0	0	0	1	b	8
3	0	3	2	siggb	0	1	0	0	0	0	s	1
0	15	4	2	gb	0	0	0	1	1	0	s	1
2	4	2	1	siggb	1	1	0	0	1	1	b	8
);
  std::istringstream tests(allPairsTests);
  // skip the initial line with the parameter names.
  {
    char const* params[] = {
      "spairQueue", "reducerType", "divLookup", "monTable",
      "buchberger", "postponeKoszul", "useBaseDivisors", "autoTailReduce",
      "autoTopReduce", "preferSparseReducers", "useSingularCriterionEarly",
      "sPairGroupType", "threadCount"};

    std::string paramName;
    size_t const paramCount = sizeof(params) / sizeof(*params);
    for (size_t i = 0; i < paramCount; ++i) {
      tests >> paramName;
      // This assert will fire if you changed the order of the
      // parameters, renamed a parameter, removed a parameter or added
      // a parameter. Unless all you did was to rename a parameter,
      // don't just update the params array that the assert is based
      // on - you also need to update the code below that parses the
      // pict output because it depends on the order of the
      // parameters.
      MATHICGB_ASSERT(paramName == params[i]);
    }
  }

  while (true) {
    // parse a line of the pict file

    int spairQueue;
    tests >> spairQueue;
    if (!tests)
      break; // no more tests
    MATHICGB_ASSERT(0 <= spairQueue && spairQueue <= 3);

    int reducerType;
    tests >> reducerType;
    MATHICGB_ASSERT(0 <= reducerType && reducerType <= 30);

    int divLookup;
    tests >> divLookup;
    MATHICGB_ASSERT(1 <= divLookup && divLookup <= 4);

    int monTable;
    tests >> monTable;
    MATHICGB_ASSERT(1 <= monTable && monTable <= 4);
    
    std::string buchberger;
    tests >> buchberger;
    MATHICGB_ASSERT("gb" == buchberger && "siggb" == buchberger);

    int postponeKoszul;
    tests >> postponeKoszul;
    MATHICGB_ASSERT(0 <= postponeKoszul && postponeKoszul <= 1);

    int useBaseDivisors;
    tests >> useBaseDivisors;
    MATHICGB_ASSERT(0 <= useBaseDivisors && useBaseDivisors <= 1);

    int autoTailReduce;
    tests >> autoTailReduce;
    MATHICGB_ASSERT(0 <= autoTailReduce && autoTailReduce <= 1);

    int autoTopReduce;
    tests >> autoTopReduce;
    MATHICGB_ASSERT(0 <= autoTopReduce && autoTopReduce <= 1);

    int preferSparseReducers;
    tests >> preferSparseReducers;
    MATHICGB_ASSERT(0 <= preferSparseReducers && preferSparseReducers <= 1);

    int useSingularCriterionEarly;
    tests >> useSingularCriterionEarly;
    MATHICGB_ASSERT(0 <= useSingularCriterionEarly);
    MATHICGB_ASSERT(useSingularCriterionEarly <= 1);

    char sPairGroupType;
    tests >> sPairGroupType;
    MATHICGB_ASSERT('d' == sPairGroupType || 's' == sPairGroupType);

    int threadCount;
    tests >> threadCount;
    MATHICGB_ASSERT(0 <= threadCount);

    // Rule out combinations of parameter values that do not make sense.
    // These are asserts because pict should have already removed these
    // combinations.
    MATHICGB_ASSERT(buchberger == "gb" || !autoTopReduce);
    MATHICGB_ASSERT(buchberger == "gb" || !autoTailReduce);
    // MATHICGB_ASSERT(buchberger == "gb" || reducerType != 25);
    // MATHICGB_ASSERT(buchberger == "gb" || reducerType != 26);
    MATHICGB_ASSERT(buchberger == "siggb"  || !postponeKoszul);
    MATHICGB_ASSERT(buchberger == "siggb" || !useBaseDivisors);
    MATHICGB_ASSERT(buchberger == "siggb" || !useSingularCriterionEarly);

    // check that we have a valid reducer type
    Reducer::ReducerType red = Reducer::ReducerType(reducerType);
    MATHICGB_ASSERT(static_cast<int>(red) == reducerType);

    std::istringstream inStream(idealStr);

    Scanner in(inStream);
    auto p = MathicIO<>().readRing(true, in);
    auto& ring = *p.first;
    auto& processor = p.second;
    auto basis = MathicIO<>().readBasis(ring, false, in);
    if (processor.schreyering())
      processor.setSchreyerMultipliers(basis);

    MATHICGB_ASSERT(Reducer::makeReducerNullOnUnknown(red, ring).get() != 0);

    mgb::mtbb::task_scheduler_init scheduler(threadCount);
    if (buchberger == "gb") {
      auto reducer = Reducer::makeReducer
        (Reducer::reducerType(reducerType), ring);
      ClassicGBAlg alg(
        std::move(basis),
        *reducer,
        divLookup,
        preferSparseReducers,
        spairQueue
      );
      alg.setUseAutoTopReduction(autoTopReduce);
      alg.setUseAutoTailReduction(autoTailReduce);
      alg.setSPairGroupType(sPairGroupType == 's' ? "MinSig" : "MinDeg");
      alg.computeGrobnerBasis();
      /// the following is more reasonable but consume more time
      testNoUsefulSPoly(std::move(reducer), alg.basis());
      // std::unique_ptr<Basis> initialIdeal =
      //   alg.basis().initialIdeal();
      // EXPECT_EQ(initialIdealStr, toString(initialIdeal.get()))
      //   << reducerType << ' ' << divLookup << ' '
      //   << monTable << ' ' << postponeKoszul << ' ' << useBaseDivisors;
    } else if (buchberger == "siggb" ){
      SignatureGB alg(
        std::move(basis),
        std::move(processor),
        Reducer::reducerType(reducerType),
        divLookup,
        monTable,
        postponeKoszul,
        useBaseDivisors,
        preferSparseReducers,
        useSingularCriterionEarly,
        spairQueue
      );
      alg.computeGrobnerBasis();
      std::string sBasis(toString(alg.getGB(), 1));
      std::string sSyzTable(toString(alg.getSyzTable()));
      size_t nonSigRed = alg.getSigReductionCount() - alg.getSingularReductionCount();

      const PolyBasis& pbasis = alg.getGB()->basis();
      auto reducer = Reducer::makeReducer
        (Reducer::reducerType(reducerType), alg.getGB()->ring());
      testNoUsefulSPoly(std::move(reducer), pbasis);
      // EXPECT_EQ(sigBasisStr, toString(alg.getGB(), 1))
      //   << reducerType << ' ' << divLookup << ' '
      //   << monTable << ' ' << ' ' << postponeKoszul << ' '
      //   << useBaseDivisors;
      // EXPECT_EQ(syzygiesStr, toString(alg.getSyzTable()))
      //   << reducerType << ' ' << divLookup << ' '
      //   << monTable << ' ' << ' ' << postponeKoszul << ' '
      //   << useBaseDivisors;
      // EXPECT_EQ(nonSingularReductions, alg.getSigReductionCount() - alg.getSingularReductionCount())
      //   << reducerType << ' ' << divLookup << ' '
      //   << monTable << ' ' << ' ' << postponeKoszul << ' '
      //   << useBaseDivisors;
    }
  }
}

TEST(GB, small) {
  testGB(smallIdealComponentLastDescending(),
         idealSmallBasis, idealSmallSyzygies, idealSmallInitial, 7);
}

TEST(GB, liu_0_1) {
  testGB(liuIdealComponentLastDescending(), liu_gb_strat0_free1,
    liu_syzygies_strat0_free1, liu_initial_strat0_free1, 13);
}

TEST(GB, weispfennig97_0_4) {
  testGB(weispfennig97IdealComponentLast(true),
         weispfennig97_gb_strat0_free4,
         weispfennig97_syzygies_strat0_free4, weispfennig97_initial_strat0_free4, 31);
}

TEST(GB, weispfennig97_0_5) {
  testGB(weispfennig97IdealComponentLast(false),
         weispfennig97_gb_strat0_free5,
         weispfennig97_syzygies_strat0_free5, weispfennig97_initial_strat0_free5, 27);
}

TEST(GB, gerdt93_0_1) {
  testGB(gerdt93IdealComponentLast(false, false), gerdt93_gb_strat0_free1,
         gerdt93_syzygies_strat0_free1, gerdt93_initial_strat0_free1, 9);
}

TEST(GB, gerdt93_0_2) {
  testGB(gerdt93IdealComponentMiddle(true), gerdt93_gb_strat0_free2,
         gerdt93_syzygies_strat0_free2, gerdt93_initial_strat0_free2, 7);
}

TEST(GB, gerdt93_0_3) {
  testGB(gerdt93IdealComponentMiddle(false), gerdt93_gb_strat0_free3,
         gerdt93_syzygies_strat0_free3, gerdt93_initial_strat0_free3, 9);
}

TEST(GB, gerdt93_0_4) {
  testGB(gerdt93IdealComponentLast(true, true), gerdt93_gb_strat0_free4,
         gerdt93_syzygies_strat0_free4, gerdt93_initial_strat0_free4, 7);
}

TEST(GB, gerdt93_0_5) {
  testGB(gerdt93IdealComponentLast(false, true), gerdt93_gb_strat0_free5,
         gerdt93_syzygies_strat0_free5, gerdt93_initial_strat0_free5, 7);
}

TEST(GB, gerdt93_0_6) {
  testGB(gerdt93IdealComponentFirst(true), gerdt93_gb_strat0_free6,
         gerdt93_syzygies_strat0_free6, gerdt93_initial_strat0_free6, 7);
}

TEST(GB, gerdt93_0_7) {
  testGB(gerdt93IdealComponentFirst(false), gerdt93_gb_strat0_free7,
         gerdt93_syzygies_strat0_free7, gerdt93_initial_strat0_free7, 9);
}
