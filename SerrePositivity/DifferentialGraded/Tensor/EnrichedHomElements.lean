module
public import SerrePositivity.DifferentialGraded.Tensor.EnrichedHomAdjunction
public import SerrePositivity.DifferentialGraded.Complexes.CurryingEvaluation

/-! # 豊穣tensor–Hom同型の斉次要素での評価 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma enrichedTensorHomIso_hom_element (M : RightModule A D) (N : LeftModule A D)
    (T : Complex A) (x : D) {k r l s n : ℤ} (hl : r + k = l) (hn : s + l = n)
    (f : Homogeneous (obj A D M N) T k) (m : (M.obj (op x)).X r) (v : (N.obj x).X s) :
    (((moduleHomπ A D M (homRightModule A D N T) x).f k
      ((enrichedTensorHomIso A D M N T).hom.f k f)).v r l hl m).v s n hn v =
    f.v (r + s) n (by omega) (element A D M N x m v rfl) := by
  have hp := enrichedTensorHomEquiv_π A D (homComplex A (obj A D M N) T) M N T (𝟙 _) x
  have he := congrArg (fun h => ((h.f k f).v r l hl m).v s n hn v) hp
  change (((moduleHomπ A D M (homRightModule A D N T) x).f k
      ((enrichedTensorHomIso A D M N T).hom.f k f)).v r l hl m).v s n hn v = _ at he
  exact he.trans (curryRight_associator_apply (ι A D M N x) (𝟙 _) hl hn f m v)

end SerrePositivity.DifferentialGraded.BalancedTensor
