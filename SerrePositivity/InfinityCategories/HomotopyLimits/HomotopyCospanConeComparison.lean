module

public import SerrePositivity.InfinityCategories.HomotopyLimits.HomotopyCospanEndComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.CospanSingleFibrationComparison

/-!
概要：一脚 fibration の引き戻しから、ホモトピー可換に比較された cospan の end への同値を作る。
方針：元の極限錐の標準比較と、path 置換への厳密な自然変換の end の同値を合成する。
規約：比較先の構造射に fibration 性を追加しない。使われ方：余錐空間の極限と Hom の cospan。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {L M R L' M' R' : SSet.{u}}
  [KanComplex L] [KanComplex M] [KanComplex R]
  [KanComplex L'] [KanComplex M'] [KanComplex R']
  (f' : L' ⟶ M') (g' : R' ⟶ M') (f : L ⟶ M) (g : R ⟶ M)
  (a : L ⟶ L') (b : M ⟶ M') (c : R ⟶ R')
  (Hf : SSet.Homotopy (f ≫ b) (a ≫ f')) (Hg : SSet.Homotopy (g ≫ b) (c ≫ g'))
  (t : Cone ((AsSmall.down : AsSmall.{u} WalkingCospan ⥤ WalkingCospan) ⋙ cospan f g))

/-- 元の厳密な錐の頂点から、二つのホモトピーで比較された cospan の共通 end への射。 -/
def homotopyCospanConeComparison :
    t.pt ⟶ weightedSections (bousfieldKanWeight (AsSmall.{u} WalkingCospan))
      (cospanPathDiagram f' g') :=
  bousfieldKanConeComparison t ≫ homotopyCospanMapEnd f' g' f g a b c Hf Hg

/-- 元の錐が一脚 fibration の極限なら、path 置換した Hom の end への実際の比較射は同値。 -/
lemma homotopyCospanConeComparison_homotopyEquivalence [Fibration f] (ht : IsLimit t)
    (ha : IsSimplicialHomotopyEquivalence a) (hb : IsSimplicialHomotopyEquivalence b)
    (hc : IsSimplicialHomotopyEquivalence c) :
    IsSimplicialHomotopyEquivalence (homotopyCospanConeComparison f' g' f g a b c Hf Hg t) := by
  let H : AsSmall.{u} WalkingCospan ⥤ SSet.{u} := AsSmall.down ⋙ cospan f g
  have : Fibration (H.map
      (AsSmall.up.map WalkingCospan.Hom.inl)) := inferInstanceAs (Fibration f)
  let U := (Functor.const (AsSmall.{u} WalkingCospan)).obj (Δ[0] : SSet.{u})
  have hU : IsTerminal U := weightIsTerminalOfObj U (fun _ ↦ stdSimplex.isTerminalObj₀)
  have := weightedConeComparison_isIso_of_isTerminalWeight U hU t ht
  have : Mono (U.map (AsSmall.up.map WalkingCospan.Hom.inr)) :=
    inferInstanceAs (Mono (𝟙 (Δ[0] : SSet.{u})))
  have := weightedSections_cospan_leftFibration_kanComplex U H
  have := kanComplex_of_iso (asIso (weightedConeComparison U t)).symm
  have : KanComplex (bousfieldKanHolim H) :=
    bousfieldKanHolim_kanComplex _
  exact (bousfieldKanConeComparison_cospan_leftFibration_homotopyEquivalence _ t ht).comp
    (homotopyCospanMapEnd_homotopyEquivalence f' g' f g a b c Hf Hg ha hb hc)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
