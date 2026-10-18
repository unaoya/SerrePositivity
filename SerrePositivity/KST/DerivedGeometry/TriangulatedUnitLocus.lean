module

public import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
概要：三角左随伴の単位が同型となる対象はシフトと三角の拡張で閉じる。
方針：随伴から右随伴の整合するシフト構造を構成し、三角間の射の二つから三つの判定を使う。
規約：右随伴に先に選ばれたシフト構造との一致を入力しない。関手と単位は同じものを保つ。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の有限コホモロジー区間への帰納。
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
  {F : C ⥤ D} {G : D ⥤ C} [F.CommShift ℤ] (adj : F ⊣ G)

/--
概要：三角左随伴の単位の同型性は全ての整数シフトで保存される。
方針：随伴から構成した右随伴のシフト比較と単位の可換式を使う。
規約：左随伴のシフト構造だけを入力する。
使われ方：TT §3、Toën §3.2 の単一対象の任意の次数への移送。
-/
lemma adjunction_unit_shift_isIso (X : C) (n : ℤ) [IsIso (adj.unit.app X)] :
    IsIso (adj.unit.app (X⟦n⟧)) := by
  letI := adj.rightAdjointCommShift ℤ
  haveI : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  have : IsIso (adj.unit.app (X⟦n⟧) ≫ ((F ⋙ G).commShiftIso n).hom.app X) := by
    rw [adj.unit_app_commShiftIso_hom_app]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (((F ⋙ G).commShiftIso n).hom.app X)

/--
概要：単位の同型性は整数シフト前後で同値。
方針：単位のシフト可換式とシフト関手の同型反映性を使う。
規約：元の単位そのものについての判定。
使われ方：TT §3、Toën §3.2 の任意の一次数に集中する対象。
-/
lemma adjunction_unit_isIso_iff_shift (X : C) (n : ℤ) :
    IsIso (adj.unit.app X) ↔ IsIso (adj.unit.app (X⟦n⟧)) := by
  constructor
  · intro h
    exact adjunction_unit_shift_isIso adj X n
  · intro h
    letI := adj.rightAdjointCommShift ℤ
    haveI : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
    have : IsIso ((shiftFunctor C n).map (adj.unit.app X)) := by
      rw [← adj.unit_app_commShiftIso_hom_app]
      infer_instance
    exact isIso_of_reflects_iso (adj.unit.app X) (shiftFunctor C n)

variable [F.IsTriangulated]

/--
概要：単位が三角の両端で同型なら中央でも同型。
方針：整合する右随伴の三角構造で単位を三角の射とし、二つの成分の同型性から判定する。
規約：distinguished triangle の元の三対象を用いる。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の有限振幅の帰納。
-/
lemma adjunction_unit_triangle_isIso₂ (T : Triangle C) (hT : T ∈ distTriang C)
    [IsIso (adj.unit.app T.obj₁)] [IsIso (adj.unit.app T.obj₃)] :
    IsIso (adj.unit.app T.obj₂) := by
  letI := adj.rightAdjointCommShift ℤ
  haveI : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  haveI : G.IsTriangulated := adj.isTriangulated_rightAdjoint
  let φ : (𝟭 C).mapTriangle.obj T ⟶ (F ⋙ G).mapTriangle.obj T :=
    { hom₁ := adj.unit.app T.obj₁
      hom₂ := adj.unit.app T.obj₂
      hom₃ := adj.unit.app T.obj₃
      comm₁ := by simpa using adj.unit.naturality T.mor₁
      comm₂ := by simpa using adj.unit.naturality T.mor₂
      comm₃ := by
        dsimp
        simp only [Category.assoc, NatTrans.shift_app_comm adj.unit (1 : ℤ) T.obj₁]
        simpa only [Functor.comp_map, Functor.id_map, Category.assoc] using
          congrArg (fun f => f ≫ ((F ⋙ G).commShiftIso (1 : ℤ)).hom.app T.obj₁)
            (adj.unit.naturality T.mor₃) }
  exact isIso₂_of_isIso₁₃ φ ((𝟭 C).map_distinguished T hT) ((F ⋙ G).map_distinguished T hT)
    (by dsimp [φ]; infer_instance) (by dsimp [φ]; infer_instance)

end SerrePositivity.KST.DerivedGeometry
