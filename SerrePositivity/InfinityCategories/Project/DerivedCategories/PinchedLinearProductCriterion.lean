module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStandardSimplexMap
/-!
概要：Hom 複体の全次数での直積表示を、pinched 線形単体の直積表示へ移す。
方針：各成分の同時原像を取り、微分方程式を全射影で検査する。
規約：有限性・Small な対象圏・compact 性は仮定しない。
使われ方：D-8 c5 の加群余積の全単体の普遍性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
  {E : Type w} [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] {J : Type t} {x y : D} {a b : J → E}

lemma pinchedLinearSimplex_family_bijective
    (φ : ∀ j, _root_.SerrePositivity.DifferentialGraded.homObject R D x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R E (a j) (b j))
    (hφ : ∀ k, Function.Bijective
      (fun z : (_root_.SerrePositivity.DifferentialGraded.homObject R D x y).X k => fun j => (φ j).f k z)) (n : ℕ) :
    Function.Bijective (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R x y n =>
      fun j => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap (φ j) s) := by
  classical
  constructor
  · intro s t h
    apply Subtype.ext
    funext i
    apply (hφ i.val.2).injective
    funext j
    exact congrArg (fun q => q.val i) (congrFun h j)
  · intro s
    let f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n := fun i =>
      (hφ i.val.2).surjective (fun j => (s j).val i) |>.choose
    have hf (j : J) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearDataMap (φ j) f = (s j).val := by
      funext i
      exact congrFun ((hφ i.val.2).surjective (fun j => (s j).val i)).choose_spec j
    have heq : f ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearSubmodule R x y n := by
      intro L k hL hk
      apply (hφ (k + 1)).injective
      funext j
      have hc := ConcreteCategory.congr_hom ((φ j).comm k (k + 1))
        (f.component L k hL hk)
      change _root_.SerrePositivity.DifferentialGraded.differential R ((φ j).f k (f.component L k hL hk)) =
        (φ j).f (k + 1) (_root_.SerrePositivity.DifferentialGraded.differential R (f.component L k hL hk)) at hc
      change (φ j).f (k + 1) (_root_.SerrePositivity.DifferentialGraded.differential R (f.component L k hL hk)) =
        (φ j).f (k + 1) (f.rhs L k hk)
      rw [← hc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearDataMap_rhs]
      change differential R ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearDataMap (φ j) f).component L k hL hk) = _
      rw [hf j]
      exact (s j).equation L k hL hk
    refine ⟨⟨f, heq⟩, ?_⟩
    funext j
    exact Subtype.ext (hf j)


lemma dgStandardSimplex_family_bijective {a b : J → D}
    (φ : ∀ j, _root_.SerrePositivity.DifferentialGraded.homObject R D x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R D (a j) (b j))
    (hφ : ∀ k, Function.Bijective
      (fun z : (_root_.SerrePositivity.DifferentialGraded.homObject R D x y).X k => fun j => (φ j).f k z)) (n : ℕ) :
    Function.Bijective (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y n =>
      fun j => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStandardSimplexMap (φ j) s) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardSimplexEquiv (R := R) x y n
  let e' := Equiv.piCongrRight (fun j : J =>
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardSimplexEquiv (R := R) (a j) (b j) n).toEquiv)
  exact e'.bijective.comp
    ((pinchedLinearSimplex_family_bijective φ hφ n).comp e.symm.toEquiv.bijective)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
