module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberRotationTriangle
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Triangulated
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberPredecessor
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberTriangleIso

/-! # Distinguished triangle の回転

概要：cofiber 列の像として定義した distinguished triangle は順回転・逆回転に閉じる。
方針：回転長方形の同型と双対圏での前の列の構成を用い、代表の変更を回転関手で移す。
規約：三角圏の公理を仮定しない。使われ方：TR2 の双方向。
-/
@[expose] public section
noncomputable section
universe u
open CategoryTheory Pretriangulated MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：cofiber 三角形の回転は distinguished triangle である。
方針：回転長方形の右面の cofiber 三角形と同型にする。
規約：通常の一回シフトと負号を含む回転。使われ方：TR2 の代表上での順方向。 -/
lemma cofiberTriangle_rotate_mem {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle t ht).rotate ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberDistinguishedTriangles X := by
  let r := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberRotationRectangle t ht
  exact ⟨r.rotatedZeroTriangle, r.rotated_isCofiber, ⟨(r.triangleIsoRotate ht).symm⟩⟩

/-- 概要：任意の distinguished triangle の順回転も distinguished triangle。
方針：cofiber 代表との同型を回転関手で送り、代表の回転の所属を移す。
規約：これは TR2 の順方向のみ。使われ方：三角構造の回転公理。 -/
lemma rotate_mem_cofiberDistinguishedTriangles {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {T : Triangle (hoFunctor.obj X)} (hT : T ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberDistinguishedTriangles X) :
    T.rotate ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberDistinguishedTriangles X := by
  obtain ⟨t, ht, ⟨e⟩⟩ := hT
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.mem_cofiberDistinguishedTriangles_of_iso ((rotate (hoFunctor.obj X)).mapIso e).symm
    (cofiberTriangle_rotate_mem t ht)

/-- 概要：任意の cofiber 三角形は、別の cofiber 三角形の順回転と同型。
方針：双対回転で前の列を作り、その順回転の第一辺を元の第一辺と照合する。
規約：辺の厳密な一致を図式同型に移す。使われ方：逆回転への閉性。 -/
lemma exists_cofiberTriangle_rotate_iso {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t) :
    ∃ (d : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (hd : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence d),
      Nonempty ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle d hd).rotate ≅ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle t ht) := by
  obtain ⟨d, hd, he⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_cofiberPredecessor t ht
  let r := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberRotationRectangle d hd
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ r.rotatedZeroTriangle.square = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ t.square := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare r.diagram 0 = _
    rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare_sharedEdge, r.left_eq, he]
  obtain ⟨e⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.nonempty_cofiberTriangleIso_of_bottom_eq
    r.rotatedZeroTriangle t r.rotated_isCofiber ht hb
  exact ⟨d, hd, ⟨(r.triangleIsoRotate hd).symm ≪≫ e⟩⟩

/-- 概要：cofiber 三角形の逆回転は distinguished triangle。
方針：前の cofiber 三角形の順回転表示を逆回転関手で戻す。
規約：Mathlib の回転自己同値の単位同型を用いる。使われ方：TR2 の代表上での逆方向。 -/
lemma cofiberTriangle_invRotate_mem {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle t ht).invRotate ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberDistinguishedTriangles X := by
  obtain ⟨d, hd, ⟨e⟩⟩ := exists_cofiberTriangle_rotate_iso t ht
  exact ⟨d, hd, ⟨((invRotate (hoFunctor.obj X)).mapIso e).symm ≪≫
    (rotCompInvRot.app (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle d hd)).symm⟩⟩

/-- 概要：任意の distinguished triangle の逆回転も distinguished triangle。
方針：cofiber 代表との同型を逆回転関手で送り、代表上の所属を移す。
規約：前の列の存在は安定性から得る。使われ方：TR2 の逆方向。 -/
lemma invRotate_mem_cofiberDistinguishedTriangles {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {T : Triangle (hoFunctor.obj X)} (hT : T ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberDistinguishedTriangles X) :
    T.invRotate ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberDistinguishedTriangles X := by
  obtain ⟨t, ht, ⟨e⟩⟩ := hT
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.mem_cofiberDistinguishedTriangles_of_iso ((invRotate (hoFunctor.obj X)).mapIso e).symm
    (cofiberTriangle_invRotate_mem t ht)

/-- 概要：三角形の distinguished 性は順回転と同値。
方針：順方向の閉性と逆回転の閉性を回転自己同値の単位同型で結ぶ。
規約：cofiber 列の像という既存の定義。使われ方：Pretriangulated の回転公理 TR2。 -/
lemma cofiberDistinguishedTriangles_rotate_iff {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (T : Triangle (hoFunctor.obj X)) :
    T ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberDistinguishedTriangles X ↔ T.rotate ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberDistinguishedTriangles X := by
  refine ⟨rotate_mem_cofiberDistinguishedTriangles, fun h => ?_⟩
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.mem_cofiberDistinguishedTriangles_of_iso (rotCompInvRot.app T).symm
    (invRotate_mem_cofiberDistinguishedTriangles h)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
