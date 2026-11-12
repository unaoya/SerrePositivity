module
public import SerrePositivity.KST.SConstruction.ZeroNaturalTransformations
public import SerrePositivity.KST.SConstruction.IdentityPushoutShapes
public import SerrePositivity.KST.SConstruction.EquivalenceDiagramExactness

/-! # McCarthy ホモトピーの零 cofiber 図式
概要：恒等射の零 cofiber と零対象からの射の cofiber を coherent な関手として作る。
方針：零射の自然変換を退化した押し出し形状で引き戻す。
規約：零対象は指定するが他の cofiber の零角を固定しない。使われ方：McCarthy の λ と ι。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：指定零対象を使う二つの標準 cofiber 正方形の coherent な族。
方針：零射の自然変換を縦または横の射影で引き戻す。
規約：false は恒等射の cofiber、true は零対象からの射。使われ方：McCarthy の λ と ι。 -/
def zeroCofiberSquare {C : SSet.{u}} (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) (b : Bool) :
    C ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C :=
  curry ((identityPushoutShape b ▷ C) ≫ zeroNaturalTransformation z (!b))

/-- 概要：標準 cofiber 正方形の各角での評価を計算する。
方針：座標射影を各単体で計算し、零射の自然変換の両端を使う。
規約：false は (c,c,z,z)、true は (z,c,z,c)。使われ方：零角と入力・出力の厳密な照合。 -/
lemma zeroCofiberSquare_evaluation {C : SSet.{u}} (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) (b : Bool)
    (i j : Fin 2) :
    zeroCofiberSquare z b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j) =
      (if b then (if i = 0 then SSet.const z.vertex else 𝟙 C)
        else (if j = 0 then 𝟙 C else SSet.const z.vertex)) := by
  have h : zeroCofiberSquare z b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint (if b then i else j) C ≫ zeroNaturalTransformation z (!b) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro c
    change (zeroNaturalTransformation z (!b)).app n
      ((identityPushoutShape b).app n
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)
          n.unop.len), C.map (𝟙 n) c) = _
    rw [CategoryTheory.Functor.map_id_apply]
    cases b <;> rfl
  rw [h]
  cases b <;> fin_cases i <;> fin_cases j <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true,
      zeroNaturalTransformation_zero, zeroNaturalTransformation_one, Fin.isValue, Fin.zero_eta,
      Fin.mk_one, Fin.one_eq_zero_iff, Nat.reduceEqDiff]

/-- 概要：各標準 cofiber 正方形は押し出し。
方針：各関手頂点を座標射影による退化四角形として表す。
規約：C は quasicategory、安定性は不要。使われ方：cofiber 図式への持ち上げ。 -/
lemma zeroCofiberSquare_vertex_isPushout {C : SSet.{u}} [Quasicategory C]
    (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) (b : Bool) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsPushoutDiagramVertex ((zeroCofiberSquare z b).app (Opposite.op ⦋0⦌) c) := by
  let g : (Δ[1] : SSet.{u}) ⟶ C :=
    lift (𝟙 _) (SSet.const c) ≫ zeroNaturalTransformation z (!b)
  have he : (zeroCofiberSquare z b).app (Opposite.op ⦋0⦌) c =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (identityPushoutShape b ≫ g) := by
    apply CategoryTheory.Functor.functorHom_ext
    intro n α
    have hα : α = (SimplexCategory.const n.unop ⦋0⦌ 0).op := Subsingleton.elim _ _
    subst α
    apply ConcreteCategory.hom_ext
    intro s
    rfl
  rw [he]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C (identityPushoutShape b ≫ g)))
  rw [Equiv.symm_apply_apply]
  exact identityPushoutShape_isPushout b g

/-- 概要：標準 cofiber 正方形を cofiber 図式の圏に持ち上げる。
方針：零角の厳密な式と退化押し出しの普遍性を使う。
規約：選んだ二つの零射の自然変換を全高次単体に使う。使われ方：McCarthy の零 cofiber 関手。 -/
def zeroCofiberFunctor {C : SSet.{u}} [Quasicategory C] (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) (b : Bool) :
    C ⟶ cofiberDiagrams C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift IsCofiberDiagramVertex (zeroCofiberSquare z b) (by
    intro c
    refine ⟨?_, zeroCofiberSquare_vertex_isPushout z b c⟩
    have heq : zeroCofiberSquare z b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
        (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 1) = SSet.const z.vertex := by
      simpa using zeroCofiberSquare_evaluation z b 0 1
    have he := ConcreteCategory.congr_hom (NatTrans.congr_app heq (Opposite.op ⦋0⦌)) c
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _).app (Opposite.op ⦋0⦌)
      ((zeroCofiberSquare z b).app (Opposite.op ⦋0⦌) c) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant z.vertex 0 at he
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] at he
    have hc : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram ((zeroCofiberSquare z b).app (Opposite.op ⦋0⦌) c)) 0 1 = z.vertex := by
      have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex
        (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 1)
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram ((zeroCofiberSquare z b).app (Opposite.op ⦋0⦌) c))
      have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
          (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram ((zeroCofiberSquare z b).app (Opposite.op ⦋0⦌) c)) =
          (zeroCofiberSquare z b).app (Opposite.op ⦋0⦌) c :=
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).apply_symm_apply _
      rw [hv] at h
      change (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram ((zeroCofiberSquare z b).app (Opposite.op ⦋0⦌) c)).app
        (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 1) = _
      rw [← h]
      exact he
    rw [hc]
    exact z.isZero)

/-- 概要：標準 cofiber 関手の包含は元の正方形の族。
方針：全部分複体への持ち上げの式。
規約：全単体での厳密な等号。使われ方：入力と商の評価。 -/
lemma zeroCofiberFunctor_ι {C : SSet.{u}} [Quasicategory C] (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) (b : Bool) :
    zeroCofiberFunctor z b ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι =
      zeroCofiberSquare z b := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 概要：標準 cofiber 関手の入力の両端は恒等または指定零対象。
方針：下辺への制限と正方形の角での評価を照合する。
規約：false の入力は恒等射、true の入力は零対象からの射。使われ方：完全性の点ごとの証明。 -/
lemma zeroCofiberFunctor_input_evaluation {C : SSet.{u}} [Quasicategory C]
    (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) (b : Bool) (i : Fin 2) :
    zeroCofiberFunctor z b ≫ cofiberProjection C ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i) =
      (if b ∧ i = 0 then SSet.const z.vertex else 𝟙 C) := by
  rw [cofiberProjection]
  simp only [← Category.assoc]
  rw [zeroCofiberFunctor_ι, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt]
  change zeroCofiberSquare z b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
    (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm 0) = _
  rw [zeroCofiberSquare_evaluation]
  cases b <;> fin_cases i <;> simp

/-- 概要：標準 cofiber の商の評価は恒等または指定零対象。
方針：正方形の (1,1) の評価の式を使う。
規約：false の商は零対象、true の商は入力そのもの。使われ方：λ と ι の商の厳密な式。 -/
lemma zeroCofiberFunctor_quotient {C : SSet.{u}} [Quasicategory C]
    (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) (b : Bool) :
    zeroCofiberFunctor z b ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm 1) =
      (if b then 𝟙 C else SSet.const z.vertex) := by
  rw [← Category.assoc, zeroCofiberFunctor_ι, zeroCofiberSquare_evaluation]
  cases b <;> simp

end SerrePositivity.KST.SConstruction
