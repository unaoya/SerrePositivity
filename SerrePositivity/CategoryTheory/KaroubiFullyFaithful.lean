module

public import Mathlib.CategoryTheory.Idempotents.FunctorExtension
public import Mathlib.CategoryTheory.Retract

/-!
# 完全忠実な関手の冪等完備化

完全忠実な関手は Karoubi 包絡に延長しても完全忠実である。
像の対象の直和因子を、元の圏の冪等元に戻すことで本質像を判定する。
三角構造を仮定しない一般の圏の結果として証明する。
-/

@[expose] public section

namespace SerrePositivity

open CategoryTheory CategoryTheory.Idempotents

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)

instance karoubiExtension_faithful [F.Faithful] :
    ((functorExtension₂ C D).obj F).Faithful where
  map_injective {P Q} f g h := by
    apply Karoubi.hom_ext
    exact F.map_injective (congrArg Karoubi.Hom.f h)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance karoubiExtension_full [F.Full] [F.Faithful] :
    ((functorExtension₂ C D).obj F).Full where
  map_surjective {P Q} f := by
    let g := F.preimage f.f
    have hg : P.p ≫ g ≫ Q.p = g := by
      apply F.map_injective
      have h := f.comm
      change F.map P.p ≫ f.f ≫ F.map Q.p = f.f at h
      dsimp only [g]
      rw [F.map_comp, F.map_comp, F.map_preimage]
      exact h
    exact ⟨⟨g, hg⟩, Karoubi.hom_ext _ _ (F.map_preimage f.f)⟩

/-- 形式的直和因子は、元の対象の標準的な像の retract である。 -/
def karoubiRetract (P : Karoubi C) : Retract P ((toKaroubi C).obj P.X) :=
  ⟨P.decompId_i, P.decompId_p, P.decompId.symm⟩

/-- 完全忠実な関手の像の直和因子は、延長した関手の本質像に属する。 -/
theorem karoubiExtension_mem_essImage [F.Full] [F.Faithful]
    (P : Karoubi D) (X : C) (r : Retract P ((toKaroubi D).obj (F.obj X))) :
    ((functorExtension₂ C D).obj F).essImage P := by
  let q : X ⟶ X := F.preimage (r.r.f ≫ r.i.f)
  have hq : F.map q = r.r.f ≫ r.i.f := F.map_preimage _
  have hr : r.i.f ≫ r.r.f = P.p := congrArg Karoubi.Hom.f r.retract
  have hqq : q ≫ q = q := by
    apply F.map_injective
    rw [F.map_comp, hq]
    simp only [Category.assoc, ← Category.assoc r.i.f, hr, Karoubi.p_comp]
  let Q : Karoubi C := ⟨X, q, hqq⟩
  refine ⟨Q, ⟨?_⟩⟩
  refine { hom := ⟨r.r.f, ?_⟩
           inv := ⟨r.i.f, ?_⟩
           hom_inv_id := ?_
           inv_hom_id := ?_ }
  · change F.map q ≫ r.r.f ≫ P.p = r.r.f
    rw [hq, Category.assoc, ← Category.assoc r.i.f, hr]
    simp
  · change P.p ≫ r.i.f ≫ F.map q = r.i.f
    rw [hq, ← Category.assoc, ← Category.assoc, Karoubi.p_comp, hr]
    exact Karoubi.p_comp r.i
  · apply Karoubi.hom_ext
    exact hq.symm
  · apply Karoubi.hom_ext
    exact hr

end SerrePositivity
