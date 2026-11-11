module
public import SerrePositivity.KST.SConstruction.CoherentArrowStringInitial
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic

/-! # 合成射と二入力射の全精密化を含む共通パラメータ
概要：三つの合成列の積圏と直通列の組を構成し、その頂点包含の anodyne 性を証明する。
方針：各合成列圏の初対象を積で合わせ、nerve の初対象包含を使う。
規約：三つの精密化を独立に保持し、指定頂点の全二単体を延長できる形にする。
使われ方：元の適合三角形を全合成列パラメータへ延ばす。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {I : Type u} [SmallCategory I] {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 合成射・前の射・後の射の全合成列を独立に含む積圏。 -/
abbrev CompositionStringParameters :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString (f ≫ g) × _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f × _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString g

/-- 三つの元の直通列からなる指定頂点。 -/
def compositionStringDirect : CompositionStringParameters f g :=
  (coherentArrowStringDirect (f ≫ g), coherentArrowStringDirect f, coherentArrowStringDirect g)

/-- 元の直通列の組は、三つの精密化を同時に動かす圏の初対象。 -/
def compositionStringDirect_isInitial : IsInitial (compositionStringDirect f g) :=
  IsInitial.ofUniqueHom (fun s => (coherentArrowStringDirectTo s.1,
    coherentArrowStringDirectTo s.2.1, coherentArrowStringDirectTo s.2.2)) (by
    intro s a
    apply Prod.ext
    · exact (coherentArrowStringDirect_isInitial (f ≫ g)).hom_ext _ _
    · apply Prod.ext
      · exact (coherentArrowStringDirect_isInitial f).hom_ext _ _
      · exact (coherentArrowStringDirect_isInitial g).hom_ext _ _)

/-- 合成射の全精密化への射影。 -/
def compositionStringComposite : CompositionStringParameters f g ⥤ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString (f ≫ g) :=
  CategoryTheory.Prod.fst _ _

/-- 前の射の全精密化への射影。 -/
def compositionStringFirst : CompositionStringParameters f g ⥤ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f :=
  CategoryTheory.Prod.snd _ _ ⋙ CategoryTheory.Prod.fst _ _

/-- 後の射の全精密化への射影。 -/
def compositionStringSecond : CompositionStringParameters f g ⥤ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString g :=
  CategoryTheory.Prod.snd _ _ ⋙ CategoryTheory.Prod.snd _ _

/-- Composite 射影は、指定直通列点を同じ元の直通列点へ送る。 -/
lemma compositionStringComposite_direct :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g) ≫ nerveMap (compositionStringComposite f g) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect (f ≫ g)) := by
  apply SSet.yonedaEquiv.injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  rfl

/-- First 射影は、指定直通列点を同じ元の直通列点へ送る。 -/
lemma compositionStringFirst_direct :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g) ≫ nerveMap (compositionStringFirst f g) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect f) := by
  apply SSet.yonedaEquiv.injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  rfl

/-- Second 射影は、指定直通列点を同じ元の直通列点へ送る。 -/
lemma compositionStringSecond_direct :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g) ≫ nerveMap (compositionStringSecond f g) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect g) := by
  apply SSet.yonedaEquiv.injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  rfl

/-- 直通列の組からの頂点包含は anodyne であり、任意の Kan 標的の全境界を持ち上げる。 -/
lemma compositionStringDirect_anodyne :
    anodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g)) := by
  rw [anodyneExtensions_eq_llp_rlp]
  intro A B p hp
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint_leftAnodyne (compositionStringDirect_isInitial f g) p
  intro C D i hi
  cases hi with
  | intro i hn => exact hp _ (SSet.modelCategoryQuillen.horn_ι_mem_J _ _)

end SerrePositivity.KST.SConstruction
