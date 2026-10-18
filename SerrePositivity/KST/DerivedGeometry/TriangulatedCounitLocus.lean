module

public import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
概要：三角左随伴の余単位が同型となる対象は三角の拡張で閉じる。
方針：随伴の整合する右随伴シフト構造で余単位を三角の射とする。
規約：右随伴の関手と余単位を変更しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 のアフィン本質的全射性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits Pretriangulated
namespace SerrePositivity.KST.DerivedGeometry
variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
  [HasShift C ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]
  {F : C ⥤ D} {G : D ⥤ C} [F.CommShift ℤ] [F.IsTriangulated] (adj : F ⊣ G)

/--
概要：余単位が三角の両端で同型なら中央でも同型。
方針：余単位を三角の射にし、二つの成分の同型性で判定する。
規約：元の distinguished triangle と同じ余単位。
使われ方：TT §3、Toën §3.2 の有限コホモロジー区間での余単位。
-/
lemma adjunction_counit_triangle_isIso₂ (T : Triangle D) (hT : T ∈ distTriang D)
    [IsIso (adj.counit.app T.obj₁)] [IsIso (adj.counit.app T.obj₃)] :
    IsIso (adj.counit.app T.obj₂) := by
  letI := adj.rightAdjointCommShift ℤ
  haveI : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  haveI : G.IsTriangulated := adj.isTriangulated_rightAdjoint
  let φ : (G ⋙ F).mapTriangle.obj T ⟶ (𝟭 D).mapTriangle.obj T :=
    { hom₁ := adj.counit.app T.obj₁
      hom₂ := adj.counit.app T.obj₂
      hom₃ := adj.counit.app T.obj₃
      comm₁ := by simpa using adj.counit.naturality T.mor₁
      comm₂ := by simpa using adj.counit.naturality T.mor₂
      comm₃ := by
        dsimp
        simp only [Category.assoc, NatTrans.shift_app_comm adj.counit (1 : ℤ) T.obj₁]
        simpa only [Functor.comp_map, Functor.id_map, Category.assoc] using
          congrArg (fun f => f ≫ ((𝟭 D).commShiftIso (1 : ℤ)).hom.app T.obj₁)
            (adj.counit.naturality T.mor₃) }
  exact isIso₂_of_isIso₁₃ φ ((G ⋙ F).map_distinguished T hT) ((𝟭 D).map_distinguished T hT)
    (by dsimp [φ]; infer_instance) (by dsimp [φ]; infer_instance)

end SerrePositivity.KST.DerivedGeometry
