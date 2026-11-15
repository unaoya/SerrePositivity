module

public import SerrePositivity.EInfinity.Interface.Theory
public import SerrePositivity.BhattScholze.Perfectoidization.Interface.Derived
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SquareFunctorTransport

/-!
# BS の perfectoid 化を E∞ 代数の界面で述べる

## 概要
BS 著者版 Definition 8.2、Lemma 8.4、Proposition 8.5、Corollaries 8.12・8.14 と
Theorem 10.11 の入力を EInfinityTheory の CAlg で保持する。

## 方針
離散埋め込みと忘却の比較、離散性の認識、指定極限の保存を界面から使う。

## 規約
元の単位、H⁰ の環、指定錐の境界と頂点、通常の商を保持する。

## 使われ方
任意の EInfinityTheory 上の入力から既存の D(R) 版 導来 perfectoid 化の界面 を得る。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Perfectoidization
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.SSet _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonoidalClosed
open _root_.SerrePositivity.InfinityCategories
open _root_.SerrePositivity.BhattScholze.PerfectoidizationInterface
open scoped _root_.Simplicial
attribute [local instance] HasDerivedCategory.standard
variable (E : EInfinityTheory.{u}) (R : Type u) [CommRing R]

/-- 概要：CAlg_R 内の離散対象。
方針：通常の Under 入力の本質像を使う。規約：全頂点同型を要求。
使われ方：BS の離散時の普遍性と整代数の欄。 -/
def IsTheoryDiscrete (x : (E.CAlg R) _⦋0⦌) : Prop :=
  ∃ S : A_R R, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x ((E.discrete R).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex S)))

/-- 概要：BS の離散性と CAlg_R の通常代数の本質像の一致。
方針：同じ U の全次数比較を代入する。規約：零次以外の全整数次数。
使われ方：universal と integral の述べ直し。 -/
lemma theory_disc_forget_iff (x : (E.CAlg R) _⦋0⦌) :
    Disc R ((E.forget R).app _ x) ↔ IsTheoryDiscrete E R x := by
  unfold IsTheoryDiscrete
  rw [← E.discrete_recognition R x]
  constructor
  · intro h i hi
    exact (h i hi).of_iso
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyIso R i _) ≪≫ (HIso R i _).symm)
  · intro h i hi
    exact (h i hi).of_iso
      ((HIso R i _) ≪≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyIso R i _).symm)

/-- 概要：元の CAlg_R 単位を J 始域の実ホモトピーへ移す。
方針：全関手比較の逆と U 像を合成して代表を選ぶ。
規約：単位の二胞体の類を変更しない。
使われ方：既存 H0RingData と指定された BS 錐。 -/
def theoryUnderlyingUnit {P : algebraNerve R ⟶ E.CAlg R}
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (E.discrete R) P) :
    NatInfinity R (J R) (P ≫ E.forget R) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy ((E.discrete_forget R).inv ≫
    (SSet.mapHomotopyCategory ((ihom (algebraNerve R)).map (E.forget R))).map η)

/-- 概要：底の実単位の二胞体の回収。
方針：ホモトピー代表の仕様を使う。規約：元の単位の U 像との合成。
使われ方：代表の選択によって単位を変えていないことの確認。 -/
lemma theoryUnderlyingUnit_hom {P : algebraNerve R ⟶ E.CAlg R}
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (E.discrete R) P) :
    SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (theoryUnderlyingUnit E R η)) =
      (E.discrete_forget R).inv ≫
        (SSet.mapHomotopyCategory ((ihom (algebraNerve R)).map (E.forget R))).map η :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy_hom _

/-- 概要：同じ perfectoid 標的の CAlg_R 図式。
方針：同じ通常代数関手を離散埋め込みへ送る。規約：添字の向きを変えない。
使われ方：BS の指定極限。 -/
def theoryTargetDiagram (p : ℕ) [Fact p.Prime] (S : A_R R) :
    perfectoidTargetNerve p S.right ⟶ E.CAlg R :=
  nerveMap (targetAlgebra R p S) ≫ E.discrete R

/-- 概要：同じ perfectoid 標的図式の全関手比較。
方針：離散比較を標的関手で前合成する。規約：全単体を保持。
使われ方：指定錐の比較の境界条件。 -/
def theoryTargetDiagramForgetIso (p : ℕ) [Fact p.Prime] (S : A_R R) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (theoryTargetDiagram E R p S ≫ E.forget R) (targetDiagram R p S) :=
  (E.discrete_forget R).precomp (nerveMap (targetAlgebra R p S))

/-- 概要：実 U は元の正方形の引き戻し性を保存する。
方針：対応する指定 coherent 錐へ任意極限保存を適用する。
規約：全正方形を同じ U で後合成。使われ方：BS excision の D(R) 版。 -/
lemma theory_forget_pullback {F : Δ[1] ⊗ Δ[1] ⟶ E.CAlg R} (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (F ≫ E.forget R) := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_iff_of_diagram_eq (by simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan, Category.assoc])
    (by simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone, Category.assoc])).mp
      (E.forget_preservesLimits R (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F) hF)

variable (p : ℕ) [Fact p.Prime]

/-- 概要：CAlg_R の指定錐と、元の単位・H⁰ の乗法を保つ底の比較データ。
方針：既存 BSLimitConeData の非普遍的データを使い、全錐比較を加える。
規約：底の錐の極限性は欄に含めない。全標的・全単体の比較を保持する。
使われ方：実 U の極限保存を同じ指定錐へ適用する。 -/
structure TheoryBSLimitConeData (P : algebraNerve R ⟶ E.CAlg R)
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (E.discrete R) P)
    (h0 : H0RingData R (P ≫ E.forget R) (theoryUnderlyingUnit E R η)) (S : A_R R) where
  /-- 同じ perfectoid 標的図式上の CAlg_R 錐。 -/
  cone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (theoryTargetDiagram E R p S)
  /-- 錐頂点は元の P(S)。 -/
  vertex_eq : cone.vertex = P.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex S)
  /-- 元の単位と H⁰ の全射影の乗法整合性。 -/
  underlying : BSLimitConeData R p (P ≫ E.forget R) (theoryUnderlyingUnit E R η) h0 S
  /-- 通常の S 上の錐からの CAlg_R の比較辺。 -/
  overSource : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (theoryTargetDiagram E R p S)).Edge
    (underlying.sourceCone.postcomp (E.discrete R)) cone
  /-- 同じ CAlg_R 単位の実代表を保つ。 -/
  overSource_unit : (overSource.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (theoryTargetDiagram E R p S))).edge =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy η) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex S)).edge
  /-- U 像と既存 G1 の指定錐の全関手比較。 -/
  comparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (cone.val ≫ E.forget R) underlying.cone.val
  /-- 標的図式上の比較は完成済みの離散比較自身。 -/
  comparison_boundary : HEq
    (comparison.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] (perfectoidTargetNerve p S.right)))
    (theoryTargetDiagramForgetIso E R p S)
  /-- 頂点上では同じ P(S) の恒等比較。 -/
  comparison_vertex : HEq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app comparison
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] (perfectoidTargetNerve p S.right)).app _ (SSet.yonedaEquiv (𝟙 Δ[0]))))
    (Iso.refl (SSet.HomotopyCategory.mk (vertex R (P ≫ E.forget R) S)))

/-- 概要：G1 の結論を既存の CAlg_R で述べた BS 界面。
方針：指定極限・excision は CAlg_R、算術条件は同じ U と H⁰ で述べる。
規約：通常の非完備代数を含む。存在・文献入力・animated 環の構成は追加しない。
使われ方：toE3 により旧 D(R) 界面とその下流へ供給する。 -/
structure TheoryPerfectoidizationInterface (hR : IsIntegralPerfectoid R p) where
  perfd : algebraNerve R ⟶ E.CAlg R
  unit : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (E.discrete R) perfd
  h0 : H0RingData R (perfd ≫ E.forget R) (theoryUnderlyingUnit E R unit)
  universal : ∀ S, IsTheoryDiscrete E R (perfd.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex S)) →
    IsPerfectoidization p (h0.unit.app S).right.hom
  limitCone : ∀ S, TheoryBSLimitConeData E R p perfd unit h0 S
  limit_isLimit : ∀ S, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (limitCone S).cone
  integral : ∀ (S : A_R R),
    (letI : Algebra R S.right := S.hom.hom.toAlgebra; Algebra.IsIntegral R S.right) →
    IsTheoryDiscrete E R (perfd.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex S)) ∧
      IsIntegralPerfectoid (h0.ringFunctor.obj S).right p
  excision : ∀ {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right),
    SerrePositivity.DerivedCompletion.IsModuleComplete S.right (p : S.right)
      (ModuleCat.of S.right S.right) →
    SerrePositivity.DerivedCompletion.IsModuleComplete T.right (p : T.right)
      (ModuleCat.of T.right T.right) →
    SerrePositivity.DerivedCompletion.IsModuleComplete S.right (p : S.right)
      (ModuleCat.of S.right I) →
    ArcOutside R p f I →
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (ordinarySquare R f (quotientProjection R S I)
      (quotientProjection R T (I.map f.right.hom)) (quotientComparison R f I)
      (quotientSquare_commutes R f I) ≫ perfd)

variable {hR : IsIntegralPerfectoid R p}

/-- 概要：同じ指定 BS 錐の底の極限性。
方針：U の極限保存と全錐比較を合成する。規約：形状の制限なし。
使われ方：旧 G1 の limit_isLimit の欄。 -/
lemma TheoryBSLimitConeData.underlying_isLimit
    {P : algebraNerve R ⟶ E.CAlg R} {η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (E.discrete R) P}
    {h0 : H0RingData R (P ≫ E.forget R) (theoryUnderlyingUnit E R η)} {S : A_R R}
    (c : TheoryBSLimitConeData E R p P η h0 S) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c.cone) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c.underlying.cone :=
  (E.forget_preservesLimits R c.cone hc).of_functorIso c.comparison

/-- 概要：実 U と指定比較による旧 G1 界面の構成。
方針：離散性は本質像の比較、極限と excision は右随伴 U の保存を使う。
規約：単位・H⁰・指定錐・通常の商・非完備始域を保持する。
使われ方：CAlg_R 版の存在を供給した場合の D(R) 版の系。 -/
def TheoryPerfectoidizationInterface.toE3 (F : TheoryPerfectoidizationInterface E R p hR) :
    PerfectoidizationInterfaceE3 R p hR where
  perfd := F.perfd ≫ E.forget R
  unit := theoryUnderlyingUnit E R F.unit
  h0 := F.h0
  universal S hS := F.universal S ((theory_disc_forget_iff E R _).mp hS)
  limitCone S := (F.limitCone S).underlying
  limit_isLimit S := (F.limitCone S).underlying_isLimit E R p (F.limit_isLimit S)
  integral S hS := ⟨(theory_disc_forget_iff E R _).mpr (F.integral S hS).1, (F.integral S hS).2⟩
  excision f I hS hT hI ha := by
    simpa only [perfdSquare, Category.assoc] using
      theory_forget_pullback E R (F.excision f I hS hT hI ha)

/-- 概要：CAlg_R 版の存在から D(R) 版の存在への証明済みの還元。
方針：toE3 を適用する。規約：存在入力や引用は新設しない。
使われ方：既存の文献入力を述べ直す際の下流への橋。 -/
theorem nonempty_e3_of_theory (h : Nonempty (TheoryPerfectoidizationInterface E R p hR)) :
    Nonempty (PerfectoidizationInterfaceE3 R p hR) :=
  h.map (TheoryPerfectoidizationInterface.toE3 E R p)

end SerrePositivity.EInfinity.Perfectoidization
