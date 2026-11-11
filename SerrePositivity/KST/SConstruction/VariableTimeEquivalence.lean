module
public import SerrePositivity.KST.SConstruction.VariableTimeHomotopy

/-! # 自然同値の可変時刻での評価の可逆性
概要：点ごとに可逆な自然変換の可変時刻の評価は始点の図式と関手として同型。
方針：指定時刻の頂点が零か一かで、prism の成分を恒等辺または元の可逆辺に同定する。
規約：可逆性を明示した仮定として保持する。使われ方：object S の単体ホモトピーの gapped 性。
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

/-- 概要：可変時刻の prism の成分は、元の自然変換が点ごとに可逆なら可逆。
方針：時刻零では恒等辺、時刻一では元の辺となることを計算する。
規約：図式の添字は任意。使われ方：可変時刻の図式の関手同型。 -/
lemma variableTimeHomotopy_isInvertible {A C D : SSet.{u}} [Quasicategory D]
    {f g : C ⟶ D} (H : SSet.Homotopy f g)
    (hH : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H c).toTruncated)
    (F : A ⟶ C) (τ : A ⟶ (Δ[1] : SSet.{u})) (a : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (variableTimeHomotopy H F τ) a).toTruncated := by
  have ht : τ.app (Opposite.op ⦋0⦌) a = stdSimplex.obj₀Equiv.symm (0 : Fin 2) ∨
      τ.app (Opposite.op ⦋0⦌) a = stdSimplex.obj₀Equiv.symm (1 : Fin 2) := by
    have hc (t : Fin 2) : t = 0 ∨ t = 1 := by
      fin_cases t <;> simp
    have h := hc (stdSimplex.obj₀Equiv (τ.app (Opposite.op ⦋0⦌) a))
    rcases h with h | h
    · exact Or.inl (stdSimplex.obj₀Equiv.injective (h.trans (Equiv.apply_symm_apply _ _).symm))
    · exact Or.inr (stdSimplex.obj₀Equiv.injective (h.trans (Equiv.apply_symm_apply _ _).symm))
  have hedge : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (variableTimeHomotopy H F τ) a).edge =
      H.h.app (Opposite.op ⦋1⦌)
        (F.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant a 1),
          intervalMin.app (Opposite.op ⦋1⦌)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge, τ.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant a 1))) := by
    change H.h.app (Opposite.op ⦋1⦌)
      (F.app (Opposite.op ⦋1⦌) (SSet.Truncated.Edge.id (X := (truncation 2).obj A) a).edge,
        intervalMin.app (Opposite.op ⦋1⦌)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge,
            τ.app (Opposite.op ⦋1⦌)
              (SSet.Truncated.Edge.id (X := (truncation 2).obj A) a).edge)) = _
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one a]
  rcases ht with ht | ht
  · have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (variableTimeHomotopy H F τ) a).edge =
        (SSet.Truncated.Edge.id (X := (truncation 2).obj D)
          (f.app (Opposite.op ⦋0⦌) (F.app (Opposite.op ⦋0⦌) a))).edge := by
      rw [hedge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map τ a 1, ht, intervalMin_app_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map F a 1]
      have h₀ := ConcreteCategory.congr_hom (NatTrans.congr_app H.h₀ (Opposite.op ⦋1⦌))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (F.app (Opposite.op ⦋0⦌) a) 1)
      change H.h.app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (F.app (Opposite.op ⦋0⦌) a) 1,
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) 1) = _ at h₀
      rw [h₀, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one]
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).2
    change IsIso (SSet.Truncated.HomotopyCategory.homMk (SSet.Truncated.Edge.id _))
    rw [SSet.Truncated.HomotopyCategory.homMk_id]
    infer_instance
  · have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (variableTimeHomotopy H F τ) a).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H (F.app (Opposite.op ⦋0⦌) a)).edge := by
      rw [hedge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map τ a 1, ht, intervalMin_app_one, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map F a 1,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one]
      rfl
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).2 (hH _)

/-- 概要：点ごとに可逆な自然変換の可変時刻の図式は始点の図式と関手として同型。
方針：min の prism の点ごとの可逆性を内部 Hom の関手同型へ移す。
規約：逆変換や図式の交換の厳密な選択は要求しない。使われ方：gapped 性の輸送。 -/
def variableTimeImageIso {A C D : SSet.{u}} [Quasicategory D] {f g : C ⟶ D}
    (H : SSet.Homotopy f g)
    (hH : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H c).toTruncated)
    (F : A ⟶ C) (τ : A ⟶ (Δ[1] : SSet.{u})) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (F ≫ f) (variableTimeImage H F τ) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy (variableTimeHomotopy H F τ)
    (variableTimeHomotopy_isInvertible H hH F τ)

/-- 概要：自然同値を可変時刻で評価した gapped 図式も gapped。
方針：始点の完全関手の像と可変時刻の図式の関手同型で条件を輸送する。
規約：自然変換の点ごとの可逆性を省略しない。使われ方：object S のホモトピーの単体。 -/
lemma IsGapped.variableTimeImage {C D : SSet.{u}} [Quasicategory D] {f g : C ⟶ D}
    (H : SSet.Homotopy f g)
    (hH : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H c).toTruncated)
    (hf : PreservesCofiberData f) {n : ℕ} {F : arNerve n ⟶ C} (hF : IsGapped F)
    (τ : arNerve n ⟶ (Δ[1] : SSet.{u})) : IsGapped (variableTimeImage H F τ) :=
  (hF.postcomp_of_cofiber f hf).of_functorIso (variableTimeImageIso H hH F τ)

end SerrePositivity.KST.SConstruction
