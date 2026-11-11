module
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorExtensionSpace
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalFixedPrism
/-!
概要：部分 prism の全時刻と初期図式を固定する実評価の全高次選択空間を構成する。
方針：部分 prism と始端を pushout で貼り、left anodyne な包含の相対延長空間を取る。
規約：指定部分は任意単射。使われ方：境界指定の相対評価の可縮な全選択。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
variable {L K E B : SSet.{u}} (i : L ⟶ K) (p : E ⟶ B) (a : K ⟶ E)
variable (γ : (Δ[1] : SSet.{u}) ⊗ K ⟶ B) (G : (Δ[1] : SSet.{u}) ⊗ L ⟶ E)
variable (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 L ≫ G = i ≫ a)
/-- 部分 prism と始端を、同じ時刻零の境界で貼った指定図式。 -/
def roofPrismBoundaryMap :
    (Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) (horn 1 0).ι i).pt ⟶ E := by
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) (horn 1 0).ι i
  refine sq.isPushout.desc G (snd (horn 1 0 : SSet.{u}) K ≫ a) ?_
  change ((horn 1 0).ι ▷ L) ≫ G =
    ((horn 1 0 : SSet.{u}) ◁ i) ≫ (snd (horn 1 0 : SSet.{u}) K ≫ a)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hornOneFirst_prism_factorization]
  simp only [Category.assoc, h₀]
  simpa only [Category.assoc] using
    (congrArg (fun k => k ≫ a) (whiskerLeft_snd (horn 1 0 : SSet.{u}) i)).symm
/-- 貼った指定図式は、元の同じ全底に厳密に重なる。 -/
lemma roofPrismBoundaryMap_over
    (hG : G ≫ p = (Δ[1] ◁ i) ≫ γ) (hγ : a ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ γ) :
    roofPrismBoundaryMap i a G h₀ ≫ p =
      (Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) (horn 1 0).ι i).ι ≫ γ := by
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) (horn 1 0).ι i
  apply sq.hom_ext
  · rw [← Category.assoc, roofPrismBoundaryMap, sq.isPushout.inl_desc,
      ← Category.assoc, sq.inl_ι]
    exact hG
  · rw [← Category.assoc, roofPrismBoundaryMap, sq.isPushout.inr_desc,
      ← Category.assoc, sq.inr_ι]
    change (snd (horn 1 0 : SSet.{u}) K ≫ a) ≫ p = ((horn 1 0).ι ▷ K) ≫ γ
    rw [Category.assoc, hγ, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hornOneFirst_prism_factorization, Category.assoc]
/-- 指定部分の全時刻・始端・全底を同時に固定する、全実 prism の選択空間。 -/
def roofRelativePrismLiftSpace
    (hG : G ≫ p = (Δ[1] ◁ i) ≫ γ) (hγ : a ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ γ) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace p γ
    (Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) (horn 1 0).ι i).ι
    (roofPrismBoundaryMap i a G h₀) (roofPrismBoundaryMap_over i p a γ G h₀ hG hγ)
/-- 指定部分の全時刻を固定しても、実評価 prism の全選択空間は可縮 Kan 複体。 -/
lemma roofRelativePrismLiftSpace_isContractibleKan [Mono i] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (hG : G ≫ p = (Δ[1] ◁ i) ≫ γ) (hγ : a ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ γ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (roofRelativePrismLiftSpace i p a γ G h₀ hG hγ) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace_isContractibleKan p γ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions_pushoutObjObj_point i _) _ _
end SerrePositivity.InfinityCategories.Project.DerivedCategories
