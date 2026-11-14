module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Functoriality.DGCompositionTriangleParameterNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.UniverseTransport.UniverseSimplexFamilies
/-! # 共通宇宙での標準合成三角形の入力外延性

概要：二入力が一致する輸送済み標準合成三角形を、全三角形として同定する。
方針：二入力の積を普遍パラメーターとし、coherent 三角形の入力自然性を使う。
規約：辺や対角だけの一致で代用せず、Small 仮定を追加しない。
使われ方：単位補正の標準端と正本係数三角形を同じ全入力で照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v r
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
lemma dgGluingUliftDGCompositionTriangleFamily_input_ext (R : Type u) [CommRing R]
    (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
    {x y z : D} {K L : SSet.{max u v}} {P : SSet.{max u v r}}
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D x y) (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D y z)
    (f' : L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D x y) (g' : L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D y z)
    (a : P ⟶ (SSet.uliftFunctor.{max u v r, max u v}).obj K)
    (b : P ⟶ (SSet.uliftFunctor.{max u v r, max u v}).obj L)
    (hf : a ≫ (SSet.uliftFunctor.{max u v r, max u v}).map f =
      b ≫ (SSet.uliftFunctor.{max u v r, max u v}).map f')
    (hg : a ≫ (SSet.uliftFunctor.{max u v r, max u v}).map g =
      b ≫ (SSet.uliftFunctor.{max u v r, max u v}).map g') :
    (Δ[2] ◁ a) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexFamily.{max u v, max u v r} 2
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionTriangleFamily R D f g) =
    (Δ[2] ◁ b) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexFamily.{max u v, max u v r} 2
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionTriangleFamily R D f' g') := by
  have hpair : a ≫ (SSet.uliftFunctor.{max u v r, max u v}).map (lift f g) =
      b ≫ (SSet.uliftFunctor.{max u v r, max u v}).map (lift f' g') := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply ULift.ext
    apply Prod.ext
    · exact congrArg ULift.down (congrArg (fun k => k.app n s) hf)
    · exact congrArg ULift.down (congrArg (fun k => k.app n s) hg)
  have ht (Q : SSet.{max u v}) (l : Q ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D x y)
      (r : Q ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D y z) :
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexFamily.{max u v, max u v r} 2
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionTriangleFamily R D l r) =
      (Δ[2] ◁ (SSet.uliftFunctor.{max u v r, max u v}).map (lift l r)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexFamily.{max u v, max u v r} 2
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionTriangleFamily R D (fst _ _) (snd _ _)) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexFamily_precomp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionTriangleFamily_precomp]
    simp only [lift_fst, lift_snd]
  rw [ht K f g, ht L f' g']
  simp only [← Category.assoc, ← whiskerLeft_comp]
  rw [hpair]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
