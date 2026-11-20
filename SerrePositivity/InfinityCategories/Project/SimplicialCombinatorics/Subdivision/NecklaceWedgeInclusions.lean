module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceWedgeStructure
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceWedgeMaps

/-! # 元の wedge の構造同型と全単体的包含
概要：結合・左右単位の同型が、元の全高次単体の包含を保つことを示す。
方針：対象等号の移送は各単体の全頂点番号を保持する。
規約：零単体だけに制限しない。使われ方：K 内の augmentation の可換性。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory _root_.Simplicial SSet

/-- 対象等号による necklace 射は、全単体の元の全頂点番号を保つ。 -/
lemma necklaceEqToHom_simplex_val {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}} (h : T = U) {n : ℕ}
    (s : T.down.carrier _⦋n⦌) (i : Fin (n + 1)) :
    (((eqToHom h : T ⟶ U).map.app _ s).val i).val = (s.val i).val := by
  cases h
  rfl

/-- 元の結合同型は、全高次単体の左ブロック包含を保つ。 -/
@[reassoc] lemma necklaceAssociator_inl_inl (T U V : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) :
    T.down.wedgeInl U.down ≫ (T.down.wedge U.down).wedgeInl V.down ≫
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator T U V).hom.map = T.down.wedgeInl (U.down.wedge V.down) := by
  apply SSet.hom_ext
  intro d
  obtain ⟨⟨n⟩⟩ := d
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  apply stdSimplex.ext
  intro i
  apply Fin.ext
  exact _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceEqToHom_simplex_val
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklace_eq_of_shape (T.down.wedge_assoc U.down V.down)) _ i

/-- 元の結合同型は、全高次単体の中央ブロック包含を保つ。 -/
@[reassoc] lemma necklaceAssociator_inr_inl (T U V : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) :
    T.down.wedgeInr U.down ≫ (T.down.wedge U.down).wedgeInl V.down ≫
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator T U V).hom.map =
      U.down.wedgeInl V.down ≫ T.down.wedgeInr (U.down.wedge V.down) := by
  apply SSet.hom_ext
  intro d
  obtain ⟨⟨n⟩⟩ := d
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  apply stdSimplex.ext
  intro i
  apply Fin.ext
  exact _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceEqToHom_simplex_val
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklace_eq_of_shape (T.down.wedge_assoc U.down V.down)) _ i

/-- 元の結合同型は、全高次単体の右ブロック包含を保つ。 -/
@[reassoc] lemma necklaceAssociator_inr (T U V : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) :
    (T.down.wedge U.down).wedgeInr V.down ≫ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator T U V).hom.map =
      U.down.wedgeInr V.down ≫ T.down.wedgeInr (U.down.wedge V.down) := by
  apply SSet.hom_ext
  intro d
  obtain ⟨⟨n⟩⟩ := d
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  apply stdSimplex.ext
  intro i
  apply Fin.ext
  have h : (((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator T U V).hom.map.app _
      (((T.down.wedge U.down).wedgeInr V.down).app _ s)).val i).val =
        T.down.vertexMax + U.down.vertexMax + (s.val i).val :=
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceEqToHom_simplex_val.{u}
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklace_eq_of_shape (T.down.wedge_assoc U.down V.down)) _ i
  exact h.trans (Nat.add_assoc _ _ _)

/-- 元の左単位は、全高次単体で元の右包含の逆。 -/
@[reassoc] lemma necklaceLeftUnitor_inr (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint.down.wedgeInr T.down ≫ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceLeftUnitor T).hom.map = 𝟙 T.down.carrier := by
  apply SSet.hom_ext
  intro d
  obtain ⟨⟨n⟩⟩ := d
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  apply stdSimplex.ext
  intro i
  apply Fin.ext
  have h : (((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceLeftUnitor T).hom.map.app _
      ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint.down.wedgeInr T.down).app _ s)).val i).val = 0 + (s.val i).val :=
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceEqToHom_simplex_val.{u} (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklace_eq_of_shape T.down.single_zero_wedge) _ i
  exact h.trans (Nat.zero_add _)

/-- 元の右単位は、全高次単体で元の左包含の逆。 -/
@[reassoc] lemma necklaceRightUnitor_inl (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) :
    T.down.wedgeInl _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint.down ≫ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceRightUnitor T).hom.map = 𝟙 T.down.carrier := by
  apply SSet.hom_ext
  intro d
  obtain ⟨⟨n⟩⟩ := d
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  apply stdSimplex.ext
  intro i
  apply Fin.ext
  exact _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceEqToHom_simplex_val
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklace_eq_of_shape T.down.wedge_single_zero) _ i

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
