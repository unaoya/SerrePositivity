module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SectionsLifting
public import SerrePositivity.InfinityCategories.Core.Limit
public import SerrePositivity.InfinityCategories.Core.SliceMap

/-!
概要：頂点を固定した coherent な錐と coslice 射影の切断の対応。
方針：錐の join からの射を coslice へ curry し、逆に切断を uncurry する。
規約：strict な通常の錐に制限せず、全ての join の錐を扱う。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.4.1.6、7.5.4.6 の coherent な錐の切断模型。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {K X : SSet.{u}} {p : K ⟶ X}

/-- 概要：coherent な錐の左端への制限は、その頂点の Yoneda 表示に一致する。
方針：頂点の定義と Yoneda の両逆関係を使う。
規約：元の単体集合の quasicategory 性は要求しない。
使われ方：Kerodon 7.4.1.6、7.5.4.6 の coslice へ curry する固定条件。 -/
lemma coherentCone_inl_vertex (c : JoinCone p) :
    joinInl (Δ[0] : SSet.{u}) K ≫ c.val = SSet.yonedaEquiv.symm c.vertex := by
  rw [JoinCone.vertex_eq, Equiv.symm_apply_apply]

/-- 概要：coherent な錐はその頂点の coslice 射影の上の図式の持ち上げを定める。
方針：左端の固定条件を使って join の射を curry する。
規約：頂点は元の錐から取る。
使われ方：Kerodon 7.4.1.6、7.5.4.6 の錐から切断模型への構成。 -/
noncomputable def coherentConeCosliceSection (c : JoinCone p) :
    K ⟶ sliceUnder (SSet.yonedaEquiv.symm c.vertex) :=
  sliceUnderCurry c.val (coherentCone_inl_vertex c)

/-- 概要：錐から得た coslice への持ち上げは底で元の図式に一致する。
方針：curry の射影の式と錐の右端の固定条件を使う。
規約：底での一致は射の厳密な等式。
使われ方：Kerodon 7.4.1.6、7.5.4.6 の切断の条件。 -/
lemma coherentConeCosliceSection_projection (c : JoinCone p) :
    coherentConeCosliceSection c ≫ sliceUnderProjection (SSet.yonedaEquiv.symm c.vertex) = p := by
  rw [coherentConeCosliceSection, sliceUnderCurry_projection]
  exact c.property

/-- 概要：指定の頂点の coslice への図式の持ち上げは coherent な錐を定める。
方針：coslice の切断を uncurry し、底の条件を錐の右端の固定条件へ移す。
規約：指定頂点 x は任意の零単体。
使われ方：Kerodon 7.4.1.6、7.5.4.6 の切断から錐への構成。 -/
noncomputable def cosliceSectionCone {x : X _⦋0⦌}
    (g : K ⟶ sliceUnder (SSet.yonedaEquiv.symm x))
    (hg : g ≫ sliceUnderProjection (SSet.yonedaEquiv.symm x) = p) : JoinCone p :=
  ⟨sliceUnderUncurry g, by rw [sliceUnderUncurry_projection]; exact hg⟩

/-- 概要：coslice への切断から作った錐の頂点は指定した頂点である。
方針：uncurry の左端の固定条件を頂点の定義で評価する。
規約：同型や同値ではなく零単体の等式。
使われ方：Kerodon 7.4.1.6、7.5.4.6 の錐の頂点の保持。 -/
lemma cosliceSectionCone_vertex {x : X _⦋0⦌}
    (g : K ⟶ sliceUnder (SSet.yonedaEquiv.symm x))
    (hg : g ≫ sliceUnderProjection (SSet.yonedaEquiv.symm x) = p) :
    (cosliceSectionCone g hg).vertex = x := by
  rw [JoinCone.vertex_eq]
  change SSet.yonedaEquiv (joinInl Δ[0] K ≫ sliceUnderUncurry g) = x
  rw [sliceUnderUncurry_fixed, Equiv.apply_symm_apply]

/-- 概要：coherent な錐を coslice への切断へ移して錐へ戻すと元の錐になる。
方針：部分型の値を比較し、curry と uncurry の逆関係を使う。
規約：全ての coherent な錐に適用する。
使われ方：Kerodon 7.4.1.6、7.5.4.6 の錐側の逆関係。 -/
lemma cosliceSectionCone_coherentCone (c : JoinCone p) :
    cosliceSectionCone (coherentConeCosliceSection c)
      (coherentConeCosliceSection_projection c) = c := by
  apply Subtype.ext
  exact sliceUnderUncurry_curry _ _

/-- 概要：頂点を固定した coherent な錐と coslice 射影上の図式の持ち上げは全単射で対応する。
方針：左端を指定頂点に固定した join の射と coslice の curry の普遍性を使う。
規約：錐の頂点の条件は左端の射の等式で指定する。
使われ方：Kerodon 7.4.1.6、7.5.4.6 の coherent な錐の切断表示。 -/
noncomputable def fixedVertexConeSectionEquiv (p : K ⟶ X) (x : X _⦋0⦌) :
    {c : JoinCone p // joinInl (Δ[0] : SSet.{u}) K ≫ c.val = SSet.yonedaEquiv.symm x} ≃
      {g : K ⟶ sliceUnder (SSet.yonedaEquiv.symm x) //
        g ≫ sliceUnderProjection (SSet.yonedaEquiv.symm x) = p} where
  toFun c := ⟨sliceUnderCurry c.val.val c.property, by
    rw [sliceUnderCurry_projection]; exact c.val.property⟩
  invFun g := ⟨cosliceSectionCone g.val g.property, sliceUnderUncurry_fixed g.val⟩
  left_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    exact sliceUnderUncurry_curry c.val.val c.property
  right_inv g := by
    apply Subtype.ext
    exact sliceUnderCurry_uncurry g.val

end SerrePositivity.InfinityCategories.HomotopyLimits
