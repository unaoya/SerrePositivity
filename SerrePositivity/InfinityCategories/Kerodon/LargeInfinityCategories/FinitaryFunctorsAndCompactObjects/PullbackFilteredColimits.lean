module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PullbackAccessibilityDetection

/-!
概要：accessible cospan の引き戻しに同じ κ-filtered 余極限を構成する。
方針：指定した filtered 図式に両成分の余極限を選び、像の保存性で貼り合わせる。
規約：全小余極限の存在・保存を仮定しない。
使われ方：accessible 引き戻しと、第二脚が点である fiber の compact 候補。

対応節は Kerodon 9.2（Tag 0639）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
variable {κ : Cardinal.{u}} {E D B : SSet.{u + 1}}
    [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p)
    (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ E)
    (hD : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ D)
    (hpc : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ p) (hqc : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ q)

include hp hE hD hpc hqc

/-- 概要：両脚が保存する κ-filtered 余極限は元の引き戻しにも存在する。
方針：両成分の指定余極限を同値持ち上げで厳密に貼り合わせる。
規約：同じ κ に対する存在・保存だけを要求する。
使われ方：引き戻しの κ-accessibility の存在部分。 -/
lemma pullback_hasSmallKappaFilteredColimits :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ (pullback p q) := by
  intro K hK hκ r
  obtain ⟨ce, he⟩ := hE K (r ≫ pullback.fst p q)
  obtain ⟨cd, hd⟩ := hD K (r ≫ pullback.snd p q)
  obtain ⟨c, hc, _, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_colimitCone_pullback_with_snd p q hp r ce cd
    he (hpc K _ ce he) hd (hqc K _ cd hd)
  exact ⟨c, hc⟩

/-- 概要：同じ κ-filtered 図式の元の余錐の余極限性は両成分で判定できる。
方針：成分から作った余極限との一意同型を両射影へ写す。
規約：全小形状の余極限保存を入力にしない。
使われ方：元の射影の κ-filtered 保存と compact 性の成分判定。 -/
lemma pullback_filtered_isColimitCone_iff_components {K : SSet.{u}}
    [Quasicategory K] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ K]
    {r : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ pullback p q} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (pullback.fst p q) c) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (pullback.snd p q) c) := by
  have : InnerFibration p := hp.innerFibration
  have : InnerFibration (pullback.snd p q) :=
    ⟨innerFibrations.pullback_snd p q (InnerFibration.mem (q := p))⟩
  have : Quasicategory (pullback p q) := quasicategory_of_innerFibration (pullback.snd p q)
  constructor
  · intro hc
    obtain ⟨ce, he⟩ := hE K (r ≫ pullback.fst p q)
    obtain ⟨cd, hd⟩ := hD K (r ≫ pullback.snd p q)
    obtain ⟨c₀, hc₀, hce, hcd⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_colimitCone_pullback_with_snd p q hp r ce cd
      he (hpc K _ ce he) hd (hqc K _ cd hd)
    let e := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitConeIso c₀ c hc₀ hc
    have hcd' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone (pullback.snd p q) c₀) :=
      hcd.symm ▸ hd
    exact ⟨hce.of_vertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp r (pullback.fst p q))),
      hcd'.of_vertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp r (pullback.snd p q)))⟩
  · rintro ⟨he, hd⟩
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_of_isPullback_of_components (IsPullback.of_hasPullback p q)
      c he hd (hpc K _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (pullback.fst p q) c) he)

/-- 概要：引き戻しの第一射影は指定された κ-filtered 余極限を保存する。
方針：同じ余錐の成分判定を使う。
規約：同じ κ の保存性だけを結論する。
使われ方：accessible 引き戻し内での compact 性。 -/
lemma pullback_fst_isKappaAccessibleFunctor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ (pullback.fst p q) := by
  intro K hK hκ r c hc
  exact ((pullback_filtered_isColimitCone_iff_components p q hp hE hD hpc hqc c).mp hc).1

/-- 概要：引き戻しの第二射影も指定された κ-filtered 余極限を保存する。
方針：同じ余錐の成分判定を使う。
規約：全小余極限保存への強化を要求しない。
使われ方：点を第二脚とする fiber の compact 性。 -/
lemma pullback_snd_isKappaAccessibleFunctor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ (pullback.snd p q) := by
  intro K hK hκ r c hc
  exact ((pullback_filtered_isColimitCone_iff_components p q hp hE hD hpc hqc c).mp hc).2

/-- 概要：引き戻しへの関手の κ-filtered 保存は両成分の保存と同値。
方針：指定された余極限余錐の像を同じ引き戻し内で判定する。
規約：始域の余完備性も accessibility も仮定しない。
使われ方：accessible 引き戻しの普遍性と生成模型の包含。 -/
lemma pullback_isKappaAccessibleFunctor_iff_components {X : SSet.{u + 1}}
    (G : X ⟶ pullback p q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ G ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ (G ≫ pullback.fst p q) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ (G ≫ pullback.snd p q) := by
  constructor
  · intro hG
    exact ⟨hG.comp (pullback_fst_isKappaAccessibleFunctor p q hp hE hD hpc hqc),
      hG.comp (pullback_snd_isKappaAccessibleFunctor p q hp hE hD hpc hqc)⟩
  · rintro ⟨he, hd⟩ K hK hκ H c hc
    apply (pullback_filtered_isColimitCone_iff_components p q hp hE hD hpc hqc
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone G c)).mpr
    exact ⟨by simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone, Category.assoc] using he K H c hc,
      by simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone, Category.assoc] using hd K H c hc⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.4.5.7" (partial := stronger-hyp) "仮定：同じ濃度 μ の filtered 余極限を両脚が保存する strict categorical pullback（Lean が強い：compact 性の部分には正則 κ<μ と IsCardinalChangeBound κ μ の冪評価を追加）。結論：(1) 元の引き戻しの小 μ-filtered 余極限の存在、(2) 両成分と共通像が μ-compact なら同じ頂点が μ-compact（この条件の下で一致）。射影の保存は同じ余極限存在の宣言から得る。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.pullback_fst_isKappaAccessibleFunctor
attribute [cite HTT "5.4.5.7" (partial := stronger-hyp) "仮定：同じ濃度 μ の filtered 余極限を両脚が保存する strict categorical pullback（Lean が強い：compact 性の部分には正則 κ<μ と IsCardinalChangeBound κ μ の冪評価を追加）。結論：(1) 元の引き戻しの小 μ-filtered 余極限の存在、(2) 両成分と共通像が μ-compact なら同じ頂点が μ-compact（この条件の下で一致）。射影の保存は同じ余極限存在の宣言から得る。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.pullback_hasSmallKappaFilteredColimits
attribute [cite HTT "5.4.5.7" (partial := stronger-hyp) "仮定：同じ濃度 μ の filtered 余極限を両脚が保存する strict categorical pullback（Lean が強い：compact 性の部分には正則 κ<μ と IsCardinalChangeBound κ μ の冪評価を追加）。結論：(1) 元の引き戻しの小 μ-filtered 余極限の存在、(2) 両成分と共通像が μ-compact なら同じ頂点が μ-compact（この条件の下で一致）。射影の保存は同じ余極限存在の宣言から得る。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.pullback_snd_isKappaAccessibleFunctor
attribute [cite HTT "5.4.6.6" (partial := special) "仮定：accessible な三準圏と accessible な両脚（Lean が強い：元の平方を一方が categorical lifting を持つ strict pullback として与える）。結論：同じ引き戻しの accessibility、両射影の accessibility、およびその引き戻しへの関手の accessibility の成分判定（この模型の場合に一致）。共通の正則濃度に各保存性を上げて同じ iff を適用できる。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.pullback_fst_isKappaAccessibleFunctor
attribute [cite HTT "5.4.6.6" (partial := special) "仮定：accessible な三準圏と accessible な両脚（Lean が強い：元の平方を一方が categorical lifting を持つ strict pullback として与える）。結論：同じ引き戻しの accessibility、両射影の accessibility、およびその引き戻しへの関手の accessibility の成分判定（この模型の場合に一致）。共通の正則濃度に各保存性を上げて同じ iff を適用できる。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.pullback_isKappaAccessibleFunctor_iff_components
attribute [cite HTT "5.4.6.6" (partial := special) "仮定：accessible な三準圏と accessible な両脚（Lean が強い：元の平方を一方が categorical lifting を持つ strict pullback として与える）。結論：同じ引き戻しの accessibility、両射影の accessibility、およびその引き戻しへの関手の accessibility の成分判定（この模型の場合に一致）。共通の正則濃度に各保存性を上げて同じ iff を適用できる。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.pullback_snd_isKappaAccessibleFunctor
