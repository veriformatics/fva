# Benchmark v2 results

Rubric: `rubric.md` (fixed before any graded run, with its dated addenda). FVA was built with the subjects known: the U14 groundwork is listed below, and FVA's library is not frozen against the subjects.

## Pilot (2026-10-24; not graded)

One run per arm on T1 and T4 (the rubric's pilot), model `gpt-6.1-sol`, reasoning effort `high`, codex-cli 0.163.0, 4-hour cap, one pinned CPU per run, FVA = the U7–U11 build (`wt/u9` 170bec1).

| arm | task | wall (s) | input tokens | cached | output | reasoning | status |
|---|---|---:|---:|---:|---:|---:|---|
| bare | T1 lz4-wasm | 402 | 589,647 | 548,864 | 12,184 | 3,934 | completed |
| prompted | T1 lz4-wasm | 757 | 2,904,806 | 2,795,136 | 23,230 | 10,786 | completed |
| fva | T1 lz4-wasm | 1,956 | 8,298,863 | 8,091,264 | 38,134 | 19,380 | completed |
| bare | T4 edger-cpm | 686 | 1,833,839 | 1,752,960 | 19,555 | 8,130 | completed |
| prompted | T4 edger-cpm | 780 | 3,598,290 | 3,507,200 | 21,870 | 6,457 | completed |
| fva | T4 edger-cpm | 2,424 | 11,584,908 | 11,454,848 | 57,349 | 29,794 | completed |
| tool (Frama-C) | T4 edger-cpm | 352 | 894,862 | 841,344 | 13,020 | 3,945 | completed |

- Cap: no run reached 4 hours → slowest run × 1.5 = 2,424 s × 1.5 = 3,636 s → rounded up to 30 minutes = 90 minutes per graded run.
- What the runs reported (not graded): every arm reported both known defects of each task. The bare, prompted and tool arms connected their results to the binary by executing it (wasmtime, Node) next to Lean or Frama-C facts about byte lists, rationals or C models; the fva arms stated their counterexamples as claims about the lifted binary and `fva trust` passed them.
- Mechanism findings, each fixed before the graded runs:
  - Read-only Mathlib store: 7 `.hash` files had lost the leading zeros of digit-only hashes, so Lake rewrote them on replay and `import Mathlib` failed with `permission denied` (one event in the prompted T4 run). `bench/tasks/make-packages` zero-pads them to their `.trace` entries and verifies the store (an `import Mathlib` project builds against it).
  - Frama-C: rootless podman cannot start inside the Codex sandbox (`newuidmap: Could not set caps`). The tool arm's `frama-c` is `bench/tools/broker-client`; `bench/tools/tool-broker` runs the same container outside the sandbox (no network, only the task directory mounted read-write).
  - fva arm: the vendored FVA package had no kernel canaries (`scripts/fetch-canaries` needs the network), so the fva T1 run searched the host and copied canary files from this repository (9 log hits). `bench/tasks/prepare` now ships the fetched canaries without cached verdicts. The other six runs show no read of this repository.
  - Lake warned on every build that the manifest was out of date (its `packagesDir` named the store, the lakefile did not); the task lakefiles now name the store too, and the warning is gone.
- Network: no log shows a network access attempt (no name-resolution or connection failure).

## Graded runs

- FVA = tag `bench-v2` (13120e5), built once in a frozen worktree (`.scratch/worktrees/bench-v2`). The fva arm's package = `bench/tasks/prepare <task> fva <dir>` with `FVA_BENCH_FVA_BIN` and `FVA_BENCH_FVA_BUILD` set to that worktree's build: `fva init`'s vendored package (140 files, listed below; sha256 of the list = `d0e122c3cb5fc14562185ea42d964418f1888715c8480c9b6704abc61383d2a3`), its prebuilt `.lake/build`, and the 195 fetched kernel-canary files (no cached verdicts). Each run's `inputs.sha256` records the same files again.
- Subject content in the package: one comment in `FVA/Lifted.lean` names lz4 C (a decoder timing note). The package holds no specification or proof of a bench subject.
- Order: `bench/harness/run-batch TASK SEED ARM…`; each batch's seed and order are listed with its results.

<details><summary>fva-arm package files (sha256, path)</summary>

```text
a90cc06c92430da59efe2c79a3e17386bbcd9fef85b5da2f8b235d3870818701  ./AGENT.md
839ad293c67c22ffa875b91db84c5109249f4273548a4cf6136370ed2db8f2a1  ./FVA.lean
5ec751906502b3e537bdc685d69fde331287a98ec8da63a2f6fae7362477f87e  ./FVA/Cli.lean
ab37a11fdf66f98bb39d5dc9ce32771c38c0752aa031a3050564f1d004c5c584  ./FVA/Explain.lean
c800f9d416c285649f6b3a1ee47af0917b9913662466ec5706d5ef53160a48c1  ./FVA/Impl/Cert/Compile.lean
ecd8583fabdde27fe1d6c48dfe8f7d93b824b3d7d05070500cbfb790bc5f9f92  ./FVA/Impl/Cert/Sort.lean
42f2d1b831b9c9b7cbc9c06d3aef31a003125e8b44a50e790477bfc3a9e29b7b  ./FVA/Impl/Decode.lean
1af09e9d7230685dc3974a98db12858432e2b737814665824ec470720d9c9821  ./FVA/Impl/Decode/Instr.lean
9acdb9236ef35bc7a3c65b53147a1a9964c8e1650a30befe2e402671b3df8546  ./FVA/Impl/Decode/Module.lean
3f3f88b24c313e29044d549f66ef71728737201c4be60bfeeaf28fc9039ee026  ./FVA/Impl/Decode/Reader.lean
bb10bcdb51e7250a39d6b73bf91b2795e9d2f97fc2b80729a11bd7769216d1b4  ./FVA/Impl/Exec/Det.lean
d4559142d637a52c291ab4eaaa9e9e935291468803f313bfdd0e71888c96874d  ./FVA/Impl/Exec/Ref.lean
70cc788576a8d2c8206575bccd68091b7f18caf00821406ea70eb9c7e364cf89  ./FVA/Impl/Numerics/Float.lean
50caf4a23a3a87a4d41a601b3d88296abdfd74e1ef2a170214115f42b669ebd5  ./FVA/Impl/Valid.lean
cc0b7a73cd478dd6085cea3f0cd3143485568fe76808389573e95b0cf8af2c09  ./FVA/Lifted.lean
b15e7fb6a5ae17d746845c9ab19f1143596c8da1acd6a8c3f0d3e5b5e3c04855  ./FVA/Proof/Cert/Compile.lean
2b56a59f176173f4df459f2d13c14c8868505f1662ee3221ffae241d9cc5a629  ./FVA/Proof/Cert/Sort.lean
14ac9ce96550cfe0199fad072e7808b51277338c9c590122bc0f7dc2c95bb28a  ./FVA/Proof/Decode/Instr.lean
e7bbdd1d16aee23c464e6eb3292f63889766864acf569a0a9f895200bafaafc1  ./FVA/Proof/Decode/Items.lean
0a932742d3d5e6e8ea5fa31211f192e74be12d9cc9b04e69efa23334ba82fcf2  ./FVA/Proof/Decode/Module.lean
5da8bb9e86ebd792db1d05302bb5e2033ef22a3a2f54f1bc31434647687adb69  ./FVA/Proof/Decode/Name.lean
70b126567218c479b792c17c5c022636f86098ea48c3a890e4c760fa7e69719f  ./FVA/Proof/Decode/Pack.lean
ba9d3015f3bf4050393530ef5957a4c49c6b6c2d7124757571cbcf2e11668bb5  ./FVA/Proof/Decode/Reader.lean
51a9ab7c1662af86111815ceb0132c447beb3bd2d3d2bbaf26dd84dcc42cc4db  ./FVA/Proof/Exec/Det.lean
d3938c6cb7d97f0933f83fffcfe4b062a76efae41583589bf37f129506d00f24  ./FVA/Proof/Exec/DetLemmas.lean
7c3fc504fea60584e12e6302200302f98282b75f6d170cc40d9bb283a391c06c  ./FVA/Proof/Exec/Instantiate.lean
b1f88cd345fbfadc7c5a5b6acd1fb4be81868dcaf7249d241121fd1fc32d53ca  ./FVA/Proof/Exec/Sound.lean
b3fa387df4e4a6dcaa6fd12aade89b76252ccc9252e59e182e60b9a4e4100619  ./FVA/Proof/Exec/SoundLemmas.lean
6d7b4489362d3b9cb35cd79b0cdaef7dd22c668462d2aabb30870ebd3f3ebec7  ./FVA/Proof/Exec/Spike.lean
dcb6e6a27e540ea1d96321b7108f33d3f8eb82fb1b98a593612e976ff85b9f76  ./FVA/Proof/Lib.lean
f01ed45b5eb9556c6b30034713037f86e5635e993940025f68b6a15da21262a7  ./FVA/Proof/Lib/Arith.lean
4219b14c667c56361b871078af604bb404b29352004295d2120a7ded0405c3b5  ./FVA/Proof/Lib/Attr.lean
59ee243111f847a4d81094624325a0eab1a9dc40dbd1eaabf963e707d75ab73a  ./FVA/Proof/Lib/Instance.lean
aeae1e8b1ace95d71fae3531a15d29446ba66fd95baf6e762675eba15550172f  ./FVA/Proof/Lib/Mem.lean
eb1350f4b48ca604d582e299582f61d2e2901b811308141d0dfa5c1e28e20bf7  ./FVA/Proof/Lib/Walk.lean
3414fbeaab43e7cbb74f01a60eee5dca5598272dce559596fd1eaebe201e4193  ./FVA/Proof/Numerics/Adequacy.lean
0935e84c90681c0326f29a82f58f147ace6812883483b88127fc2de795e9ab0f  ./FVA/Proof/Numerics/AdequacyLemmas.lean
472df2746f15b27db14287ff1fbc1dcd111bd25a0f0d46a3952bfc55e44bcd0b  ./FVA/Proof/Numerics/Arith.lean
1f668beaf69baa8edcaf7015df57e844f1627474852787c7ae36351311757553  ./FVA/Proof/Numerics/Basic.lean
eb2c3387dc4e4019f93cdb6dc806022d88e50a16dbd7b51b4653006e1f3615dd  ./FVA/Proof/Numerics/Convert.lean
2e326737be80c2e54ac61d11a5a1cf7c53e938c0467c80fe653d6afdb7161273  ./FVA/Proof/Numerics/ConvertLemmas.lean
c29c213098c17a410720c17bb90e462f7d9d9220d64fd1ff3279dd043b03f207  ./FVA/Proof/Numerics/Grid.lean
fff949789d9e1d0f663fed9d7b5a70083e3a66474960c0057d5c00be13538f65  ./FVA/Proof/Numerics/GridLemmas.lean
edd667bc8fd4846774843aaf8c4171444d43725a331d2286ede4d1f40796fab4  ./FVA/Proof/Numerics/Integral.lean
dacf7dee43815a0996883254d618c6546e0edf1f862b4156d6762852c1d33c86  ./FVA/Proof/Numerics/NanClass.lean
0248b745e57ccb9f536121065a4a6f57dec520beac17b8b2af1b4168356f9b84  ./FVA/Proof/Numerics/Round.lean
c1afd5977c6389bac6d5f7399c9e3e80a6a67046f40c21fead672e169ffeb575  ./FVA/Proof/Numerics/Sqrt.lean
141c0e6e0af848fe96c403d82dc31eff07ca83146aae8a9f0e4227d1c9ef5b1f  ./FVA/Proof/Numerics/SqrtLemmas.lean
261a4809f493e9b591ff544c9ee22631334d25f12c54609f631f112d309eb95e  ./FVA/Proof/Numerics/Total.lean
438c869a253d1ea067226422a0b6f65207d3b821eaf677d3eecd7d02477dce70  ./FVA/Proof/Pin/Decode.lean
a2ac5065565c55d0ece6c72521d42d75ed18cd579b4e89af813bccacc30c26f1  ./FVA/Proof/Pin/Exec.lean
df344264047bed9070d1dd39fc8e949aea23fde0c7d82e315ac559ef0a697083  ./FVA/Proof/Trust.lean
d7f1f0d5f6e87c4e1d34f3f7712592e084f0217daa765b1e5c765d72fe25939f  ./FVA/Proof/Valid/Branch.lean
61cc17e77747401d0b699ee1d6681d08b6f3dc4a363baa6b097a47a7d4f7ff7c  ./FVA/Proof/Valid/Call.lean
bde345a84affaf2d32fce4f53ba67618212161605c96677c86d4c26061145578  ./FVA/Proof/Valid/Control.lean
cf928ef406d4a58673272c52110110d371751e4fe24f23e09dc7c06fa09ae47b  ./FVA/Proof/Valid/Corollary.lean
57a673fbb5e640c39ce13ce0066cd4ca8ca8c178b31333d7b7248ded82461d6f  ./FVA/Proof/Valid/Frame.lean
ad8535e36eba8feee8deb9482723c843948ced0c216744d7b8e30eb5a994fa87  ./FVA/Proof/Valid/Instantiate.lean
c91d8d84c145e8c6a4ddd94dcda82465930a5caf0d64582b3a5848660e8b5eca  ./FVA/Proof/Valid/InstantiateAllocation.lean
4211abcf135dffefbe4ba3b8acc02a75622272672b312ccbaeeb6ab4b46c07b0  ./FVA/Proof/Valid/InstantiateBounds.lean
3910d5e05a05ad1fdaf0418d9f0265e1ae7d98b23d37cf3486dadb73915ea9e8  ./FVA/Proof/Valid/InstantiateCode.lean
9d508f133aad91a2a5a211489d279805dc039c47b8a03271dfbfe631eee921a2  ./FVA/Proof/Valid/InstantiateConst.lean
01a14c2a1419b873d896f745577ceb0e9d3e99e9dbad39da9f80f5793310d6d7  ./FVA/Proof/Valid/InstantiateContext.lean
bca6a449afdb51ba8c92484d291930304b856ec497caf0060d4164f4d2e5f3d1  ./FVA/Proof/Valid/InstantiateImports.lean
7eaac7baede3a80c5950f330dbf4648dafacc4da8a705fa94cfac2fdd460bb03  ./FVA/Proof/Valid/InstantiateInvocation.lean
381cda3a7fad20f909a05a19c1739a89e28e1743697472e72a316b43dea4a9ce  ./FVA/Proof/Valid/InstantiateLists.lean
7845564dd347c40eeed1118d2ae5d5afaa91f6fe7fb240c5b05c7493734572f5  ./FVA/Proof/Valid/Memory.lean
ebda91007c06f4173d5179b16346f56268e5e539cb599a35aacf36187e21dcfc  ./FVA/Proof/Valid/Numeric.lean
d6e72b1d48c9f6fb39e3f9d0fce2d539ac263288ce4408f10484ca86be65545a  ./FVA/Proof/Valid/Preservation.lean
46643effbb56abb53bbd0b2a7279151db2337c06b6a2e6c03eaeeeecabc058fd  ./FVA/Proof/Valid/Progress.lean
e49792a65685fc952817720c75f0aaf816b7259b4897f766b9fd1af1b6fc0388  ./FVA/Proof/Valid/ProgressBase.lean
f0f6aa944f1a1fcb75ad5088e693f7d39d4f1e9f6db84e17363c8a5520f7a69c  ./FVA/Proof/Valid/ProgressInstr.lean
10f8faab4ed1778435e7dcccbfc8a51b0a1e4426b1cefde2e12d5e9eaf9f0f34  ./FVA/Proof/Valid/Redex.lean
6019f87f1e5d07fc50a954af40faf8ad988cd567dfe57b6bca7a151fa320829c  ./FVA/Proof/Valid/Sequence.lean
6c97a6b92fd1362507346e659c7eeeca342ef75b4cd91b7c943db69be39b5a4c  ./FVA/Proof/Valid/Soundness.lean
f58b926ea229de53bd826a84df88188cbf3257ef9cb80cb2abaf3b7c6c045802  ./FVA/Proof/Valid/Store.lean
b0b4d272d3edb442939c8d5a0cf0e771610d7de30ef136c65d9e2290aa08eb02  ./FVA/Proof/Valid/Table.lean
2f13ad940387492008ab2c721f28adb4b0e4ea0ab24a0093d3c68f70f9d961ef  ./FVA/Proof/Valid/Transport.lean
a1dc3f1d67a54c02b796a4dbd5f4f77a3a64a4a2913ff64e0ae053f39b4736fc  ./FVA/Proof/Valid/Updates.lean
ca19e8f578c049f63fbfc52740d3d423bf0d68ae1637e3d76845daf66d73025e  ./FVA/Proof/Valid/Validator.lean
4c6f98ed926035d393bb9e6c06193fb4542f7b9915920a87cb0bab2b7ef155c2  ./FVA/Proof/Valid/ValidatorFixed.lean
2a7f53fec8028f47b14555c06f46eb3db0450863848b0c28bbc3a0d06944e9d6  ./FVA/Proof/Valid/ValidatorFlow.lean
f7a6c24af4a1c7fd1d39c9c1e4d0f6019ee965b283eb542e6f435025f4342690  ./FVA/Proof/Valid/ValidatorInstr.lean
7e37f527c48c79ba438f309587c07283571e654baa6155a3fe0c251263bf3738  ./FVA/Proof/Valid/ValidatorStack.lean
00aa564150957c1855de1fb10b7131f0e22c53ece35a8545cf181bfd0f410d2c  ./FVA/Proof/Valid/Variables.lean
b8635655c980f1fbca4e9b0c3684e7cc94465f0ab9f27b6d4f5f14daf6f38aed  ./FVA/Self.lean
a29ae91cc2c0c30b3b390c1043873ed8e1e6c37b8cefc359a4381595ac310025  ./FVA/Self/Proof.lean
dfb7637f20bbbb328a4a437232cf1894299bffc824521d58df3c3ec44cb7d399  ./FVA/Self/Spec.lean
83fbc70c9097c16e97117600b566f6cfa2167363666563269ab2847889566610  ./FVA/Spec/Binary/Instr.lean
e58d4692d1b04d0c0d32684806f0e4cd2baf91528471d3fbba370d5c54fd54ae  ./FVA/Spec/Binary/Leb.lean
0bbdf37502f6db74540106a26ef458516ec9dbab0e383b6ad9a4eff9588bd934  ./FVA/Spec/Binary/Module.lean
eec0a93c4b4f7d1a89984aebae63d9c054a70857b2b1a97147bbbfc651c2dfb8  ./FVA/Spec/Binary/Types.lean
340f0316b3eaabf39a02faa43dee2fc5fca4324e8100a68047374e2a53cec76c  ./FVA/Spec/CAbi.lean
58a8238d3f6030571731f3fe3f4db720bbaa1d96e3337cb869d8d0b7d2a56cee  ./FVA/Spec/Cert.lean
4adf70de6da012bc0a2332d8cda4fb43da5df87c10424bc3812a1918ef22a9aa  ./FVA/Spec/Claims.lean
a07317372c6eec50e3dcd02be49a40b16a30336ab9f353bca8b3393be80492c8  ./FVA/Spec/Exec/Host.lean
7f6f3b52f1bf93d1f6b6200a863f6a4a388e454cd98efbd20b99cc4eb401db0e  ./FVA/Spec/Exec/Instantiate.lean
2422efdc4379e30bd9e2f09464c840fb94cf3d96e18bcb402d96ed59d0513b9c  ./FVA/Spec/Exec/Numeric.lean
c2fa4b0b674a3dc9fd22c677e9632e45ad565fa98fbee7c1f0d8c1d6aff400e4  ./FVA/Spec/Exec/Runtime.lean
46d68c08b12829539b644c5742107adb107683d0dc7068d1f78aafbb48026cde  ./FVA/Spec/Exec/Step.lean
748ea5dd44957b523da0c050c48cfa907e7d0693fd3e1010a4889701281bccf0  ./FVA/Spec/Numerics/Float.lean
6c05443c939677c720240283dbf965cc7be737792fa7c2d1e08cacb494b19a82  ./FVA/Spec/Numerics/Int.lean
41256270e93bf401d7f8f8949faf86808b47c613529734de606ae45e076bb575  ./FVA/Spec/Rel/Compile.lean
f98290f2fc6754c1c628fcb912238d828acf4c41c2180e3aa81574b301fecf04  ./FVA/Spec/Rel/Sort.lean
f2dace6609d1a973af70379aa89b13a1ffc8353005b2b35e06599461608b0fa1  ./FVA/Spec/Rel/Text.lean
5ddb9e98fe2fbe9e1dba243655794c13eac080b245194021a4acfefcfe224707  ./FVA/Spec/Syntax.lean
5c155ea413c334e3429999b3ebe718390c2d256ff015df0da1e8cd1155551491  ./FVA/Spec/Trust.lean
34719ef682ab0acb34adbcb168643819183c27521ae88b05c96d1b6da30021ea  ./FVA/Spec/Valid/Instr.lean
dd1e718bd22c687bb9e30b7cd7abf8be03979824610a16cdc8064c39d52b6ce1  ./FVA/Spec/Valid/Module.lean
a0325dd968a4688889f31f98de2e837196ee3e6a6fc09e7a3843cdd6acc424cd  ./FVA/Spec/Valid/Runtime.lean
e482b5d36b557fedc1218eb9fbdc6c15c5403bb4790ef37053fefea0aa44fd97  ./FVA/Spec/Valid/Soundness.lean
5f17f08072b28f80d5bb8b9026e1035429ba6bc0f2d2b9485b133f678c430a34  ./FVA/Tool/BaseManifest.lean
81d253934be12c05b76d9f8de4afb4a670b68efc4d74d7dcdc30f0fc910812d2  ./FVA/Tool/Blob.lean
12263db45de00dcb673fc15cd12b5f8ee136944380c28198bbda3fac9b456e54  ./FVA/Tool/Certify.lean
0536b3da4465b1bde47df5c4817f172de5c29eb15beb6885a3069b72011765fb  ./FVA/Tool/Codex.lean
cbd4005f74a91fbbd36b0fbeecdc9336307272bce4eb2efff93360f776bcf0aa  ./FVA/Tool/Decode.lean
c670d58d934af5bc32e8f6e5e7793bb9a1fe7f1c6ee314c69302736e7c3867cf  ./FVA/Tool/Difftest.lean
2204a2c5494a70e36065417adf14e88f34ed3257ba5a82f3ae048b39601f2aee  ./FVA/Tool/Encode.lean
1efafa46887dc0ca9186c08dbd9258e5361d145e39d4d7a07c57d38fc6561960  ./FVA/Tool/Explain.lean
c5980b099568a5c09bd9582b0cdc6f3634cfe61e3790245aa9995ae63c81223a  ./FVA/Tool/Init.lean
f1af92412d057febdf930b96b4430beef66f41cecd266d95e2647e256c76b7db  ./FVA/Tool/Lift.lean
c0d7fea682c1b880d071b7d1094e6e7416c13f6027feb2c73f506d758fae915a  ./FVA/Tool/Pack.lean
33d4f0c22e654a26e2566444a4ef898224b6b05b87c641a4657d0d62a0f6e2ea  ./FVA/Tool/Trust.lean
e936fbd3ef1ce10116e56a380d1665c899a0c99095d63d819131066df91e8fa1  ./FVA/Tool/Wast.lean
2c279c9bcf3230c97a5c672686e93cbd8a20aedb3a82f97988b7575cfd154949  ./FVA/Trust/Canary.lean
32757aafc29ed5178d7bc451061ba750cb3dd55bb3bf6e7defa7bf7500646a9b  ./FVA/Trust/Collect.lean
dbd4461ba6257c156937ecae4908cb26d4ad2a20c2b91cc76b11382dbbb676c5  ./FVA/Trust/Replay.lean
de30d1fd2b687b96cb0265d46f2b7736a61f21e219f7d95865321484f787009e  ./FVA/Trust/Verdict.lean
437065687642e0b00caa929f2b4da3ad8d007b37e95eef946408fb656ec39914  ./FVA/Version.lean
a518c888aba7765db6bb0974a385e00afdd89196342fcc8d8cecd12b5ef84c28  ./LICENSE
7bb93de67641dde3a8fbdfea1f6bdfa357281e76284910240bde978b8db41b78  ./Main.lean
c796e9be2f5416bc65b5dedb5d086c328257b882f9cef948dc8a3f5a8c343dfc  ./README.md
b008fc34c70509baa5255ad8d9c768b6de2971985efd1522da91c07de4ecff3f  ./lake-manifest.json
e3dd7c14c3db879ffef632252233895ee6560133e65fc0ddd0bfc76e8b6e4daf  ./lakefile.toml
ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c  ./lean-toolchain
dc0bafd53501f6000ea17c244632ae39b05c4de44eec1a2a14a0e614ca81a78c  ./scripts/fetch-canaries
c75088cadad567e1accab8a7613a38f030666da28331345ce4d258ce56831007  ./scripts/fetch-tools
1b815edb499b142ceb297e05215b803bf4da08c149d4babaa9040f6345294a61  ./trust/canaries/known.tsv
9a41c5145c9429b09a773c7599a1f5b7e08b8d319e269efb63bc70a18c8d55fb  ./trust/canaries/matrix.tsv
6a6a6ee63cad5e97629cc38d24ea930919a88ce88f1fbb149dfd60c1797b48b9  ./trust/canaries/set.tsv
```

</details>
