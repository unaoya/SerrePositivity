module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberTriangle

/-! # Cofiber 列の像で定義する distinguished triangle

概要：cofiber 列から構成した三角形と同型な三角形の集合を定義する。
方針：通常の Triangle の同型による閉包を取り、同型不変性を証明する。
規約：前加法構造・シフトの加法性と残る三角圏公理は別途必要。Pretriangulated は導入しない。
使われ方：S4 の三角構造の distinguishedTriangles の候補。
-/
@[expose] public section
noncomputable section
universe u
open CategoryTheory Pretriangulated SSet
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：cofiber 列の像と同型な三角形からなる集合。
方針：構成した cofiberTriangle の三角形同型による閉包を取る。
規約：三角圏の公理は別途必要。使われ方：将来の Pretriangulated の distinguishedTriangles。 -/
def cofiberDistinguishedTriangles (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    Set (Triangle (hoFunctor.obj X)) :=
  {T | ∃ (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t), Nonempty (T ≅ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle t ht)}

/-- 概要：cofiber 列から構成した三角形は指定した集合に属する。
方針：同じ三角形の恒等同型を使う。
規約：これは TR1 全体ではない。使われ方：distinguished の基本的な代表。 -/
lemma cofiberTriangle_mem_cofiberDistinguishedTriangles {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle t ht ∈ cofiberDistinguishedTriangles X := ⟨t, ht, ⟨Iso.refl _⟩⟩

/-- 概要：cofiber の像として指定した三角形の集合は同型に閉じている。
方針：二つの三角形同型を合成する。
規約：実際の Triangle の同型を使う。使われ方：distinguished の同型不変性。 -/
lemma mem_cofiberDistinguishedTriangles_of_iso {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {T U : Triangle (hoFunctor.obj X)} (e : T ≅ U) (h : T ∈ cofiberDistinguishedTriangles X) :
    U ∈ cofiberDistinguishedTriangles X := by
  obtain ⟨t, ht, ⟨i⟩⟩ := h
  exact ⟨t, ht, ⟨e.symm ≪≫ i⟩⟩

/-- 概要：同型な三角形は cofiber の像として指定した集合への所属が同値。
方針：同型とその逆による不変性を両向きに適用する。
規約：前加法構造は不要。使われ方：distinguished の判定の輸送。 -/
lemma cofiberDistinguishedTriangles_iso_iff {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {T U : Triangle (hoFunctor.obj X)} (e : T ≅ U) :
    T ∈ cofiberDistinguishedTriangles X ↔ U ∈ cofiberDistinguishedTriangles X :=
  ⟨mem_cofiberDistinguishedTriangles_of_iso e, mem_cofiberDistinguishedTriangles_of_iso e.symm⟩

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
