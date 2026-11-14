module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianEdgeTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InvertibleCartesian
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IntervalBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction

/-!
概要：左の輸送と右の輸送を比較する正方形の二側面を組み立てる。
方針：時刻零では恒等輸送、時刻一では指定された右の輸送を区間の境界上で貼る。
規約：全パラメータ・底・終点・Cartesian 性を保持する。使われ方：自然な単位の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open _root_.CategoryTheory MonoidalCategory CartesianMonoidalCategory _root_.SSet
open scoped _root_.Simplicial
namespace SerrePositivity.InfinityCategories.HTT.Section2_4_1
noncomputable section

/-- 正方形の境界因子と輸送の時間因子を交換する。 -/
def comparisonBoundaryExchange (A : SSet.{u}) :
    (Δ[1] : SSet.{u}) ⊗ ((boundary 1 : SSet.{u}) ⊗ A) ⟶
      (boundary 1 : SSet.{u}) ⊗ ((Δ[1] : SSet.{u}) ⊗ A) where
  app _ := ↾(fun ⟨s, t, x⟩ ↦ (t, s, x))
  naturality := by intros; rfl

/-- 時刻零の恒等輸送と時刻一の指定輸送からなる二側面の図式。 -/
def cartesianComparisonBoundary {A E : SSet.{u}}
    (H K : (Δ[1] : SSet.{u}) ⊗ A ⟶ E) :
    (Δ[1] : SSet.{u}) ⊗ ((boundary 1 : SSet.{u}) ⊗ A) ⟶ E :=
  _root_.SerrePositivity.InfinityCategories.HTT.Section2_4_1.comparisonBoundaryExchange A ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram (snd (Δ[1] : SSet.{u}) A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ H) K

/-- 零の側面は、左の輸送の始点における恒等輸送。 -/
lemma cartesianComparisonBoundary_zero {A E : SSet.{u}}
    (H K : (Δ[1] : SSet.{u}) ⊗ A ⟶ E) :
    ((Δ[1] : SSet.{u}) ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 0 A) ≫
      _root_.SerrePositivity.InfinityCategories.HTT.Section2_4_1.cartesianComparisonBoundary H K = snd (Δ[1] : SSet.{u}) A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ H := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, x⟩
  change (if (0 : Fin 2) = 0 then
    H.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) d, x) else
    K.app _ (s, x)) = H.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) d, x)
  simp only [↓reduceIte]

/-- 一の側面は、元の指定した右の輸送。 -/
lemma cartesianComparisonBoundary_one {A E : SSet.{u}}
    (H K : (Δ[1] : SSet.{u}) ⊗ A ⟶ E) :
    ((Δ[1] : SSet.{u}) ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 1 A) ≫
      _root_.SerrePositivity.InfinityCategories.HTT.Section2_4_1.cartesianComparisonBoundary H K = K := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, x⟩
  change (if (1 : Fin 2) = 0 then
    H.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) d, x) else
    K.app _ (s, x)) = K.app _ (s, x)
  simp only [show ¬ (1 : Fin 2) = 0 from by decide, ↓reduceIte]

/-- 二つの輸送の終点が同じなら、二側面の終点は元の左の輸送の境界である。 -/
lemma cartesianComparisonBoundary_target {A E : SSet.{u}}
    (H K : (Δ[1] : SSet.{u}) ⊗ A ⟶ E)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ K = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ H) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ _root_.SerrePositivity.InfinityCategories.HTT.Section2_4_1.cartesianComparisonBoundary H K = ((boundary 1).ι ▷ A) ≫ H := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, x⟩
  have ht : t.val = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (t.val 0)) d := by
    apply SSet.stdSimplex.ext
    intro j
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.boundaryOne_simplex_constant t j
  have hk := congrArg (fun f ↦ f.app (Opposite.op ⦋d⦌) x) h
  change (if t.val 0 = 0 then
    H.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) d, x) else
    K.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 1) d, x)) = H.app _ (t.val, x)
  split_ifs with h0
  · exact congrArg (fun z ↦ H.app (Opposite.op ⦋d⦌) (z, x))
      (ht.trans (congrArg (fun i : Fin 2 ↦
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm i) d) h0)).symm
  · have h1 : t.val 0 = 1 := by
      apply Fin.ext
      change (t.val 0).val = 1
      have hn := (t.val 0).isLt
      have hz : (t.val 0).val ≠ 0 := fun h ↦ h0 (Fin.ext h)
      omega
    exact hk.trans (congrArg (fun z ↦ H.app (Opposite.op ⦋d⦌) (z, x))
      (ht.trans (congrArg (fun i : Fin 2 ↦
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm i) d) h1)).symm)

/-- 二側面の底は、標準区間の最小値で与える比較正方形の底に一致する。 -/
lemma cartesianComparisonBoundary_base {A E : SSet.{u}}
    (p : E ⟶ (Δ[1] : SSet.{u}))
    (H K : (Δ[1] : SSet.{u}) ⊗ A ⟶ E)
    (hH : H ≫ p = fst (Δ[1] : SSet.{u}) A)
    (hK : K ≫ p = fst (Δ[1] : SSet.{u}) A) :
    _root_.SerrePositivity.InfinityCategories.HTT.Section2_4_1.cartesianComparisonBoundary H K ≫ p =
      ((Δ[1] : SSet.{u}) ◁ ((boundary 1).ι ▷ A)) ≫
        ((Δ[1] : SSet.{u}) ◁ fst (Δ[1] : SSet.{u}) A) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismFirstContraction 1 := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t, x⟩
  change p.app _ (if t.val 0 = 0 then
    H.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) d, x) else
    K.app _ (s, x)) = _
  split_ifs with ht
  · have hh := congrArg (fun f ↦ f.app (Opposite.op ⦋d⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) d, x)) hH
    change p.app _ (H.app _ (_, x)) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) d at hh
    rw [hh]
    apply SSet.stdSimplex.ext
    intro j
    change 0 = if s j = 0 then 0 else t.val j
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.boundaryOne_simplex_constant t j, ht]
    split_ifs <;> rfl
  · have hh := congrArg (fun f ↦ f.app (Opposite.op ⦋d⦌) (s, x)) hK
    change p.app _ (K.app _ (s, x)) = s at hh
    rw [hh]
    apply SSet.stdSimplex.ext
    intro j
    change s j = if s j = 0 then 0 else t.val j
    split_ifs with hs
    · exact hs
    · have ht1 : t.val 0 = 1 := by
        apply Fin.ext
        change (t.val 0).val = 1
        have hn := (t.val 0).isLt
        have hz : (t.val 0).val ≠ 0 := fun h ↦ ht (Fin.ext h)
        omega
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.boundaryOne_simplex_constant t j, ht1]
      apply Fin.ext
      change (s j).val = 1
      have hn := (s j).isLt
      have hz : (s j).val ≠ 0 := fun h ↦ hs (Fin.ext h)
      omega

/-- inner fibration に関して、定値辺は Cartesian である。 -/
lemma isCartesianEdge_constant {E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
    (p : E ⟶ B) [InnerFibration p] (x : E _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1) := by
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (SSet.Truncated.Edge.id (X := (truncation 2).obj E) x) := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk
      (SSet.Truncated.Edge.id (X := (truncation 2).obj E) x))
    rw [SSet.Truncated.HomotopyCategory.homMk_id]
    infer_instance
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_of_isInvertibleEdge p _ hi

/-- 指定した右の輸送が Cartesian なら、二側面の全垂直辺も Cartesian である。 -/
lemma cartesianComparisonBoundary_vertical {A E : SSet.{u}}
    (p : E ⟶ (Δ[1] : SSet.{u})) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration p]
    (H K : (Δ[1] : SSet.{u}) ⊗ A ⟶ E)
    (hK : ∀ x : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p
      (K.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1)))
    (v : ((boundary 1 : SSet.{u}) ⊗ A) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p ((_root_.SerrePositivity.InfinityCategories.HTT.Section2_4_1.cartesianComparisonBoundary H K).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1)) := by
  have : Quasicategory E := quasicategory_of_innerFibration p
  rcases v with ⟨t, x⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p (if t.val 0 = 0 then
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ H).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1) else
    K.app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1))
  split_ifs
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map]
    exact _root_.SerrePositivity.InfinityCategories.HTT.Section2_4_1.isCartesianEdge_constant p _
  · exact hK x

/-- 二側面の始点は、元の二つの輸送の始点を境界へ貼った図式である。 -/
lemma cartesianComparisonBoundary_source {A E : SSet.{u}}
    (H K : (Δ[1] : SSet.{u}) ⊗ A ⟶ E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ _root_.SerrePositivity.InfinityCategories.HTT.Section2_4_1.cartesianComparisonBoundary H K =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ H) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ K) := by rfl

end
end SerrePositivity.InfinityCategories.HTT.Section2_4_1

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "2.4.1.6"] _root_.SerrePositivity.InfinityCategories.HTT.Section2_4_1.isCartesianEdge_constant
