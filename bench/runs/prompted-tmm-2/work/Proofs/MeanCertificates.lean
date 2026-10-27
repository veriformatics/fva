import Proofs.Computation
import Proofs.LogCertificates
namespace TMM
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cert0 : List Term := [⟨(4388 / 6305 : ℚ),(152215444069520 / 17026875850041 : ℚ),(-45309 / 125000 : ℚ),(-362463 / 1000000 : ℚ)⟩,⟨(5485 / 7566 : ℚ),(82999020 / 15145747 : ℚ),(-6433 / 20000 : ℚ),(-321643 / 1000000 : ℚ)⟩,⟨(6582 / 8827 : ℚ),(58099314 / 17884085 : ℚ),(-293481 / 1000000 : ℚ),(-146737 / 500000 : ℚ)⟩,⟨(8776 / 11349 : ℚ),(199197648 / 23346613 : ℚ),(-128557 / 500000 : ℚ),(-64277 / 250000 : ℚ)⟩,⟨(1097 / 1261 : ℚ),(18475480049863284381312193586291 / 497956444937642435266839393692 : ℚ),(-139327 / 1000000 : ℚ),(-69661 / 500000 : ℚ)⟩,⟨(10970 / 11349 : ℚ),(124498530 / 26070803 : ℚ),(-2123 / 62500 : ℚ),(-33963 / 1000000 : ℚ)⟩,⟨(6582 / 6305 : ℚ),(82999020 / 15145747 : ℚ),(2687 / 62500 : ℚ),(42997 / 1000000 : ℚ)⟩,⟨(5485 / 5044 : ℚ),(27666340 / 4134231 : ℚ),(16763 / 200000 : ℚ),(4191 / 50000 : ℚ)⟩,⟨(9873 / 8827 : ℚ),(87148971 / 21984518 : ℚ),(22397 / 200000 : ℚ),(11199 / 100000 : ℚ)⟩,⟨(4388 / 3783 : ℚ),(33199608 / 9654923 : ℚ),(74177 / 500000 : ℚ),(148359 / 1000000 : ℚ)⟩,⟨(7679 / 6305 : ℚ),(48416095 / 8258637 : ℚ),(24643 / 125000 : ℚ),(197149 / 1000000 : ℚ)⟩,⟨(3291 / 2522 : ℚ),(67600843324785356841593612742 / 2242104858355879010839496809 : ℚ),(133069 / 500000 : ℚ),(266143 / 1000000 : ℚ)⟩,⟨(8776 / 6305 : ℚ),(55332680 / 17888801 : ℚ),(165337 / 500000 : ℚ),(8267 / 25000 : ℚ)⟩,⟨(5485 / 3783 : ℚ),(85743507094830 / 15162056372267 : ℚ),(74299 / 200000 : ℚ),(371503 / 1000000 : ℚ)⟩,⟨(7679 / 5044 : ℚ),(77465752 / 15150463 : ℚ),(84057 / 200000 : ℚ),(52537 / 125000 : ℚ)⟩]
theorem cert0_valid : ∀ t ∈ cert0, t.valid := by
  intro t ht
  simp only [cert0, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, log6⟩
  · exact ⟨by norm_num, log11⟩
  · exact ⟨by norm_num, log12⟩
  · exact ⟨by norm_num, log17⟩
  · exact ⟨by norm_num, log26⟩
  · exact ⟨by norm_num, log35⟩
  · exact ⟨by norm_num, log41⟩
  · exact ⟨by norm_num, log46⟩
  · exact ⟨by norm_num, log48⟩
  · exact ⟨by norm_num, log53⟩
  · exact ⟨by norm_num, log60⟩
  · exact ⟨by norm_num, log68⟩
  · exact ⟨by norm_num, log73⟩
  · exact ⟨by norm_num, log77⟩
  · exact ⟨by norm_num, log82⟩
theorem mean0_bounds : ((39 / 2000 : ℚ) : ℝ) ≤ meanLog grouped0 ∧ meanLog grouped0 ≤ ((1 / 50 : ℚ) : ℝ) := by
  have h := mean_bounds cert0 cert0_valid (by norm_num [weights, cert0])
  have heq : cert0.map (fun t => (t.q,t.w)) = grouped0 := by rfl
  rw [heq] at h
  constructor
  · exact le_trans (by norm_num [lowMean, weights, cert0]) h.1
  · exact le_trans h.2 (by norm_num [highMean, weights, cert0])
def cert1 : List Term := [⟨(1097 / 1242 : ℚ),(3882387375162 / 276580087055 : ℚ),(-124147 / 1000000 : ℚ),(-62071 / 500000 : ℚ)⟩,⟨(4388 / 4347 : ℚ),(38149272 / 7445503 : ℚ),(1173 / 125000 : ℚ),(9389 / 1000000 : ℚ)⟩,⟨(1097 / 1035 : ℚ),(3406185 / 904021 : ℚ),(29087 / 500000 : ℚ),(58179 / 1000000 : ℚ)⟩,⟨(2194 / 1863 : ℚ),(16941504468906 / 1277441766557 : ℚ),(81767 / 500000 : ℚ),(163539 / 1000000 : ℚ)⟩,⟨(1097 / 828 : ℚ),(10899792 / 1582681 : ℚ),(140659 / 500000 : ℚ),(70331 / 250000 : ℚ)⟩,⟨(7679 / 5589 : ℚ),(4768659 / 599531 : ℚ),(158843 / 500000 : ℚ),(79423 / 250000 : ℚ)⟩,⟨(4388 / 3105 : ℚ),(40874220 / 6096773 : ℚ),(345857 / 1000000 : ℚ),(43233 / 125000 : ℚ)⟩,⟨(5485 / 3726 : ℚ),(13624740 / 2480689 : ℚ),(193339 / 500000 : ℚ),(193343 / 500000 : ℚ)⟩,⟨(1097 / 621 : ℚ),(1137334602828341451904641 / 35445007650371738522020 : ℚ),(568983 / 1000000 : ℚ),(71127 / 125000 : ℚ)⟩]
theorem cert1_valid : ∀ t ∈ cert1, t.valid := by
  intro t ht
  simp only [cert1, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, log28⟩
  · exact ⟨by norm_num, log39⟩
  · exact ⟨by norm_num, log42⟩
  · exact ⟨by norm_num, log55⟩
  · exact ⟨by norm_num, log69⟩
  · exact ⟨by norm_num, log72⟩
  · exact ⟨by norm_num, log74⟩
  · exact ⟨by norm_num, log79⟩
  · exact ⟨by norm_num, log86⟩
theorem mean1_bounds : ((73 / 250 : ℚ) : ℝ) ≤ meanLog grouped1 ∧ meanLog grouped1 ≤ ((117 / 400 : ℚ) : ℝ) := by
  have h := mean_bounds cert1 cert1_valid (by norm_num [weights, cert1])
  have heq : cert1.map (fun t => (t.q,t.w)) = grouped1 := by rfl
  rw [heq] at h
  constructor
  · exact le_trans (by norm_num [lowMean, weights, cert1]) h.1
  · exact le_trans h.2 (by norm_num [highMean, weights, cert1])
def cert2 : List Term := [⟨(1097 / 1359 : ℚ),(1490823 / 460478 : ℚ),(-214173 / 1000000 : ℚ),(-26771 / 125000 : ℚ)⟩,⟨(4388 / 5285 : ℚ),(23190580 / 9058729 : ℚ),(-186003 / 1000000 : ℚ),(-92999 / 500000 : ℚ)⟩,⟨(3291 / 3775 : ℚ),(496941 / 263924 : ℚ),(-137211 / 1000000 : ℚ),(-68603 / 500000 : ℚ)⟩,⟨(1097 / 1208 : ℚ),(1325176 / 427719 : ℚ),(-96389 / 1000000 : ℚ),(-96383 / 1000000 : ℚ)⟩,⟨(2194 / 2265 : ℚ),(1263507364252730085390 / 69880614569167654007 : ℚ),(-31851 / 1000000 : ℚ),(-15923 / 500000 : ℚ)⟩,⟨(1097 / 1057 : ℚ),(1159529 / 394960 : ℚ),(37143 / 1000000 : ℚ),(37147 / 1000000 : ℚ)⟩,⟨(3291 / 3020 : ℚ),(29816460 / 5775421 : ℚ),(42967 / 500000 : ℚ),(85939 / 1000000 : ℚ)⟩,⟨(4388 / 3775 : ℚ),(2650352 / 296683 : ℚ),(150469 / 1000000 : ℚ),(75237 / 500000 : ℚ)⟩,⟨(1097 / 906 : ℚ),(993882 / 362201 : ℚ),(47823 / 250000 : ℚ),(2989 / 15625 : ℚ)⟩,⟨(7679 / 6040 : ℚ),(46381160 / 12319813 : ℚ),(60021 / 250000 : ℚ),(240089 / 1000000 : ℚ)⟩,⟨(1097 / 755 : ℚ),(4880200148329118299333289205895 / 109373707477179686129421653106 : ℚ),(373613 / 1000000 : ℚ),(373621 / 1000000 : ℚ)⟩]
theorem cert2_valid : ∀ t ∈ cert2, t.valid := by
  intro t ht
  simp only [cert2, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, log22⟩
  · exact ⟨by norm_num, log23⟩
  · exact ⟨by norm_num, log27⟩
  · exact ⟨by norm_num, log31⟩
  · exact ⟨by norm_num, log36⟩
  · exact ⟨by norm_num, log40⟩
  · exact ⟨by norm_num, log47⟩
  · exact ⟨by norm_num, log54⟩
  · exact ⟨by norm_num, log59⟩
  · exact ⟨by norm_num, log65⟩
  · exact ⟨by norm_num, log78⟩
theorem mean2_bounds : ((1821 / 10000 : ℚ) : ℝ) ≤ meanLog grouped2 ∧ meanLog grouped2 ≤ ((913 / 5000 : ℚ) : ℝ) := by
  have h := mean_bounds cert2 cert2_valid (by norm_num [weights, cert2])
  have heq : cert2.map (fun t => (t.q,t.w)) = grouped2 := by rfl
  rw [heq] at h
  constructor
  · exact le_trans (by norm_num [lowMean, weights, cert2]) h.1
  · exact le_trans h.2 (by norm_num [highMean, weights, cert2])
def cert3 : List Term := [⟨(1 / 1 : ℚ),(347821577836425306012402868061 / 833354674084022804972818560 : ℚ),(0 / 1 : ℚ),(1 / 250000 : ℚ)⟩]
theorem cert3_valid : ∀ t ∈ cert3, t.valid := by
  intro t ht
  simp only [cert3, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl
  · exact ⟨by norm_num, log37⟩
theorem mean3_bounds : ((-1 / 5000 : ℚ) : ℝ) ≤ meanLog grouped3 ∧ meanLog grouped3 ≤ ((3 / 10000 : ℚ) : ℝ) := by
  have h := mean_bounds cert3 cert3_valid (by norm_num [weights, cert3])
  have heq : cert3.map (fun t => (t.q,t.w)) = grouped3 := by rfl
  rw [heq] at h
  constructor
  · exact le_trans (by norm_num [lowMean, weights, cert3]) h.1
  · exact le_trans h.2 (by norm_num [highMean, weights, cert3])
def cert4 : List Term := [⟨(1097 / 1916 : ℚ),(20551548470229367534783767947506979286108269524 / 470926308324223327128929827548199027157140545 : ℚ),(-22307 / 40000 : ℚ),(-139411 / 250000 : ℚ)⟩,⟨(12067 / 19160 : ℚ),(115601860 / 21903731 : ℚ),(-462357 / 1000000 : ℚ),(-231171 / 500000 : ℚ)⟩,⟨(9873 / 15328 : ℚ),(37833336 / 8878637 : ℚ),(-109971 / 250000 : ℚ),(-43987 / 100000 : ℚ)⟩,⟨(3291 / 4790 : ℚ),(31527780 / 11514991 : ℚ),(-187671 / 500000 : ℚ),(-375333 / 1000000 : ℚ)⟩,⟨(12067 / 17244 : ℚ),(208083348 / 41738753 : ℚ),(-5578 / 15625 : ℚ),(-44623 / 125000 : ℚ)⟩,⟨(5485 / 7664 : ℚ),(2627315 / 390331 : ℚ),(-334519 / 1000000 : ℚ),(-20907 / 62500 : ℚ)⟩,⟨(1097 / 1437 : ℚ),(9458334 / 1834601 : ℚ),(-134991 / 500000 : ℚ),(-33747 / 125000 : ℚ)⟩,⟨(7679 / 9580 : ℚ),(73564820 / 25116769 : ℚ),(-221189 / 1000000 : ℚ),(-221183 / 1000000 : ℚ)⟩,⟨(4388 / 5269 : ℚ),(92481488 / 14054929 : ℚ),(-18297 / 100000 : ℚ),(-36593 / 200000 : ℚ)⟩,⟨(3291 / 3832 : ℚ),(302364425902992552147 / 17949195198787291127 : ℚ),(-761 / 5000 : ℚ),(-30439 / 200000 : ℚ)⟩,⟨(18649 / 21076 : ℚ),(393046324 / 58288425 : ℚ),(-24469 / 200000 : ℚ),(-122339 / 1000000 : ℚ)⟩,⟨(2194 / 2395 : ℚ),(21018520 / 6800889 : ℚ),(-43829 / 500000 : ℚ),(-87653 / 1000000 : ℚ)⟩,⟨(5485 / 5748 : ℚ),(3689563266862860 / 279704382441451 : ℚ),(-23419 / 500000 : ℚ),(-46833 / 1000000 : ℚ)⟩,⟨(7679 / 7664 : ℚ),(7356482 / 2879501 : ℚ),(1951 / 1000000 : ℚ),(489 / 250000 : ℚ)⟩,⟨(14261 / 13412 : ℚ),(191268532 / 41762857 : ℚ),(30689 / 500000 : ℚ),(61383 / 1000000 : ℚ)⟩,⟨(18649 / 17244 : ℚ),(643166712 / 54187163 : ℚ),(9791 / 125000 : ℚ),(19583 / 250000 : ℚ)⟩,⟨(1097 / 958 : ℚ),(28608237978840064663 / 1298302552158398080 : ℚ),(135483 / 1000000 : ℚ),(2117 / 15625 : ℚ)⟩,⟨(14261 / 11496 : ℚ),(81972228 / 19850087 : ℚ),(215527 / 1000000 : ℚ),(53883 / 250000 : ℚ)⟩,⟨(12067 / 9580 : ℚ),(231203720 / 33463917 : ℚ),(46159 / 200000 : ℚ),(577 / 2500 : ℚ)⟩,⟨(9873 / 7664 : ℚ),(9458334 / 3401951 : ℚ),(50653 / 200000 : ℚ),(253271 / 1000000 : ℚ)⟩,⟨(7679 / 5748 : ℚ),(5532891504316848 / 436470574144147 : ℚ),(57927 / 200000 : ℚ),(289641 / 1000000 : ℚ)⟩]
theorem cert4_valid : ∀ t ∈ cert4, t.valid := by
  intro t ht
  simp only [cert4, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, log0⟩
  · exact ⟨by norm_num, log1⟩
  · exact ⟨by norm_num, log3⟩
  · exact ⟨by norm_num, log5⟩
  · exact ⟨by norm_num, log7⟩
  · exact ⟨by norm_num, log9⟩
  · exact ⟨by norm_num, log14⟩
  · exact ⟨by norm_num, log20⟩
  · exact ⟨by norm_num, log24⟩
  · exact ⟨by norm_num, log25⟩
  · exact ⟨by norm_num, log29⟩
  · exact ⟨by norm_num, log32⟩
  · exact ⟨by norm_num, log33⟩
  · exact ⟨by norm_num, log38⟩
  · exact ⟨by norm_num, log43⟩
  · exact ⟨by norm_num, log45⟩
  · exact ⟨by norm_num, log51⟩
  · exact ⟨by norm_num, log61⟩
  · exact ⟨by norm_num, log63⟩
  · exact ⟨by norm_num, log67⟩
  · exact ⟨by norm_num, log70⟩
theorem mean4_bounds : ((-199 / 1250 : ℚ) : ℝ) ≤ meanLog grouped4 ∧ meanLog grouped4 ≤ ((-1587 / 10000 : ℚ) : ℝ) := by
  have h := mean_bounds cert4 cert4_valid (by norm_num [weights, cert4])
  have heq : cert4.map (fun t => (t.q,t.w)) = grouped4 := by rfl
  rw [heq] at h
  constructor
  · exact le_trans (by norm_num [lowMean, weights, cert4]) h.1
  · exact le_trans h.2 (by norm_num [highMean, weights, cert4])
def cert5 : List Term := [⟨(1097 / 1704 : ℚ),(197030054755824 / 9622867858123 : ℚ),(-220203 / 500000 : ℚ),(-440393 / 1000000 : ℚ)⟩,⟨(3291 / 4544 : ℚ),(7477152 / 2174137 : ℚ),(-322621 / 1000000 : ℚ),(-161307 / 500000 : ℚ)⟩,⟨(7679 / 10224 : ℚ),(78510096 / 19798393 : ℚ),(-286251 / 1000000 : ℚ),(-57249 / 200000 : ℚ)⟩,⟨(1097 / 1420 : ℚ),(18692880 / 2792767 : ℚ),(-129041 / 500000 : ℚ),(-64519 / 250000 : ℚ)⟩,⟨(9873 / 12496 : ℚ),(123373008 / 24702773 : ℚ),(-235609 / 1000000 : ℚ),(-58901 / 250000 : ℚ)⟩,⟨(5485 / 6816 : ℚ),(37385760 / 6820561 : ℚ),(-217259 / 1000000 : ℚ),(-108627 / 500000 : ℚ)⟩,⟨(1097 / 1136 : ℚ),(55524723568934987144022794391503580048937464323536 / 996683039970272571768490937369743978899093866235 : ℚ),(-34937 / 1000000 : ℚ),(-8733 / 250000 : ℚ)⟩,⟨(7679 / 6816 : ℚ),(26170032 / 8053355 : ℚ),(119213 / 1000000 : ℚ),(59609 / 500000 : ℚ)⟩,⟨(3291 / 2840 : ℚ),(37385760 / 6820561 : ℚ),(73693 / 500000 : ℚ),(147391 / 1000000 : ℚ)⟩,⟨(12067 / 10224 : ℚ),(123373008 / 24702773 : ℚ),(82867 / 500000 : ℚ),(165739 / 1000000 : ℚ)⟩,⟨(5485 / 4544 : ℚ),(12461920 / 2792767 : ℚ),(37641 / 200000 : ℚ),(18821 / 100000 : ℚ)⟩,⟨(9873 / 7952 : ℚ),(78510096 / 19798393 : ℚ),(27047 / 125000 : ℚ),(216381 / 1000000 : ℚ)⟩,⟨(1097 / 852 : ℚ),(11215728 / 2174137 : ℚ),(252747 / 1000000 : ℚ),(15797 / 62500 : ℚ)⟩,⟨(3291 / 2272 : ℚ),(29908608 / 3108781 : ℚ),(185263 / 500000 : ℚ),(185267 / 500000 : ℚ)⟩,⟨(12067 / 7952 : ℚ),(95956784 / 22259515 : ℚ),(417047 / 1000000 : ℚ),(417057 / 1000000 : ℚ)⟩,⟨(1097 / 710 : ℚ),(6230960 / 2013897 : ℚ),(435061 / 1000000 : ℚ),(435073 / 1000000 : ℚ)⟩,⟨(5485 / 3408 : ℚ),(37385760 / 9936041 : ℚ),(475883 / 1000000 : ℚ),(475899 / 1000000 : ℚ)⟩]
theorem cert5_valid : ∀ t ∈ cert5, t.valid := by
  intro t ht
  simp only [cert5, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, log2⟩
  · exact ⟨by norm_num, log10⟩
  · exact ⟨by norm_num, log13⟩
  · exact ⟨by norm_num, log16⟩
  · exact ⟨by norm_num, log18⟩
  · exact ⟨by norm_num, log21⟩
  · exact ⟨by norm_num, log34⟩
  · exact ⟨by norm_num, log50⟩
  · exact ⟨by norm_num, log52⟩
  · exact ⟨by norm_num, log56⟩
  · exact ⟨by norm_num, log58⟩
  · exact ⟨by norm_num, log62⟩
  · exact ⟨by norm_num, log66⟩
  · exact ⟨by norm_num, log76⟩
  · exact ⟨by norm_num, log81⟩
  · exact ⟨by norm_num, log83⟩
  · exact ⟨by norm_num, log85⟩
theorem mean5_bounds : ((-51 / 2000 : ℚ) : ℝ) ≤ meanLog grouped5 ∧ meanLog grouped5 ≤ ((-1 / 40 : ℚ) : ℝ) := by
  have h := mean_bounds cert5 cert5_valid (by norm_num [weights, cert5])
  have heq : cert5.map (fun t => (t.q,t.w)) = grouped5 := by rfl
  rw [heq] at h
  constructor
  · exact le_trans (by norm_num [lowMean, weights, cert5]) h.1
  · exact le_trans h.2 (by norm_num [highMean, weights, cert5])
def cert6 : List Term := [⟨(3291 / 4876 : ℚ),(32093832 / 9332909 : ℚ),(-19657 / 50000 : ℚ),(-39313 / 100000 : ℚ)⟩,⟨(7679 / 10971 : ℚ),(252738927 / 21249980 : ℚ),(-356769 / 1000000 : ℚ),(-356761 / 1000000 : ℚ)⟩,⟨(6582 / 8533 : ℚ),(56164206 / 17286887 : ℚ),(-129803 / 500000 : ℚ),(-649 / 2500 : ℚ)⟩,⟨(8776 / 10971 : ℚ),(96281496 / 22566379 : ℚ),(-55809 / 250000 : ℚ),(-22323 / 100000 : ℚ)⟩,⟨(1097 / 1219 : ℚ),(157172732586822434133619095820841594748950817 / 2985239344734791914156887987170052378430190 : ℚ),(-52727 / 500000 : ℚ),(-105449 / 1000000 : ℚ)⟩,⟨(6582 / 6095 : ℚ),(40117290 / 14640193 : ℚ),(19217 / 250000 : ℚ),(76873 / 1000000 : ℚ)⟩,⟨(5485 / 4876 : ℚ),(320227628835220 / 47725869208083 : ℚ),(117691 / 1000000 : ℚ),(1839 / 15625 : ℚ)⟩,⟨(4388 / 3657 : ℚ),(32093832 / 9332909 : ℚ),(182229 / 1000000 : ℚ),(91117 / 500000 : ℚ)⟩,⟨(7679 / 6095 : ℚ),(46803505 / 15965856 : ℚ),(115509 / 500000 : ℚ),(231023 / 1000000 : ℚ)⟩,⟨(3291 / 2438 : ℚ),(533789796977868 / 44334403748113 : ℚ),(300009 / 1000000 : ℚ),(60003 / 200000 : ℚ)⟩,⟨(8776 / 6095 : ℚ),(53489720 / 17291519 : ℚ),(364549 / 1000000 : ℚ),(364557 / 1000000 : ℚ)⟩,⟨(5485 / 3657 : ℚ),(100293225 / 10663204 : ℚ),(50671 / 125000 : ℚ),(202689 / 500000 : ℚ)⟩,⟨(7679 / 4876 : ℚ),(74885608 / 14644825 : ℚ),(90831 / 200000 : ℚ),(454169 / 1000000 : ℚ)⟩]
theorem cert6_valid : ∀ t ∈ cert6, t.valid := by
  intro t ht
  simp only [cert6, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, log4⟩
  · exact ⟨by norm_num, log8⟩
  · exact ⟨by norm_num, log15⟩
  · exact ⟨by norm_num, log19⟩
  · exact ⟨by norm_num, log30⟩
  · exact ⟨by norm_num, log44⟩
  · exact ⟨by norm_num, log49⟩
  · exact ⟨by norm_num, log57⟩
  · exact ⟨by norm_num, log64⟩
  · exact ⟨by norm_num, log71⟩
  · exact ⟨by norm_num, log75⟩
  · exact ⟨by norm_num, log80⟩
  · exact ⟨by norm_num, log84⟩
theorem mean6_bounds : ((17 / 10000 : ℚ) : ℝ) ≤ meanLog grouped6 ∧ meanLog grouped6 ≤ ((11 / 5000 : ℚ) : ℝ) := by
  have h := mean_bounds cert6 cert6_valid (by norm_num [weights, cert6])
  have heq : cert6.map (fun t => (t.q,t.w)) = grouped6 := by rfl
  rw [heq] at h
  constructor
  · exact le_trans (by norm_num [lowMean, weights, cert6]) h.1
  · exact le_trans h.2 (by norm_num [highMean, weights, cert6])
end TMM
