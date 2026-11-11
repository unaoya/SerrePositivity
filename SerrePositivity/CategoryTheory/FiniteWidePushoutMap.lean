module

public import SerrePositivity.CategoryTheory.FiniteWidePushout
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# 基底の下の関手による有限広押し出しの保存

## 概要
一脚を加える押し出しを保つ関手は、同じ射を有限個並べた広押し出しを保つ。

## 方針
基底の下の圏で押し出しの脚を読み、二項押し出しの保存から帰納する。

## 規約
基底の下の関手は指定した射の二項押し出しを保てばよい。

## 使われ方
BS 著者版 Corollary 3.12 の有限剰余での Čech 余脈体の比較。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v u' v'

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {X Y : C}

/-- 基底の恒等射から指定の構造射への一意な射。 -/
abbrev fromBase {Z : C} (g : X ⟶ Z) : Under.mk (𝟙 X) ⟶ Under.mk g :=
  (Under.mkIdInitial (X := X)).to (Under.mk g)

/-- 広い span の個々の脚を基底の下の射として取る。 -/
abbrev repeatedWideUnderLeg {f : X ⟶ Y} {n : ℕ} (s : Cocone (repeatedWideSpan f n)) (i : Fin n) :
    Under.mk f ⟶ Under.mk (s.ι.app none) :=
  Under.homMk (s.ι.app (some i)) (by exact s.w (WidePushoutShape.Hom.init i))

/-- 概要：広押し出しの cocone を基底の下で関手によって移す。
方針：各射は基底脚を保つので、基底の下の圏の射になる。
規約：空の添字でも基底脚を残す。
使われ方：完備 Čech 余脈体の有限剰余。 -/
@[expose] def mapRepeatedWideCocone (F : Under X ⥤ D) {f : X ⟶ Y} {n : ℕ}
    (s : Cocone (repeatedWideSpan f n)) :
    Cocone (repeatedWideSpan (F.map (fromBase f)) n) :=
  WidePushoutShape.mkCocone (F.map (fromBase (s.ι.app none)))
    (fun i ↦ F.map (repeatedWideUnderLeg s i)) (fun i ↦ by
      change F.map (fromBase f) ≫ F.map (repeatedWideUnderLeg s i) = _
      rw [← F.map_comp]
      congr 1
      exact (Under.mkIdInitial (X := X)).hom_ext _ _)

private def mapRepeatedWideCoconeIso (F : Under X ⥤ D) {f : X ⟶ Y} {n : ℕ}
    {s t : Cocone (repeatedWideSpan f n)} (e : s ≅ t) :
    mapRepeatedWideCocone F s ≅ mapRepeatedWideCocone F t := by
  have he (k) : s.ι.app k ≫ e.hom.hom = t.ι.app k := e.hom.w k
  let E : Under.mk (s.ι.app none) ≅ Under.mk (t.ι.app none) :=
    Under.isoMk ((Cocone.forget _).mapIso e) (he none)
  refine Cocone.ext (F.mapIso E) ?_
  rintro (_ | i)
  · change F.map (fromBase _) ≫ F.map E.hom = F.map (fromBase _)
    rw [← F.map_comp]
    congr 1
    exact (Under.mkIdInitial (X := X)).hom_ext _ _
  · change F.map (repeatedWideUnderLeg s i) ≫ F.map E.hom = F.map (repeatedWideUnderLeg t i)
    rw [← F.map_comp]
    congr 1
    ext : 1
    exact he (some i)

/-- 概要：各二項押し出しを保つなら指定した射の有限広押し出しを保つ。
方針：押し出しを一脚ずつ構成し、余極限の同型で任意の選択へ移す。
規約：関手は基底の下の圏に定義する。
使われ方：BS 著者版 Corollary 3.12 の完備 Čech 余脈体の有限剰余。 -/
def isColimit_mapRepeatedWideCocone (F : Under X ⥤ D) (f : X ⟶ Y)
    (hex : ∀ ⦃Z : C⦄ (g : X ⟶ Z), HasPushout f g)
    (hmap : ∀ ⦃Z W : C⦄ (g : X ⟶ Z) (i : Y ⟶ W) (j : Z ⟶ W)
      (h : IsPushout f g i j),
      IsPushout (F.map (fromBase f)) (F.map (fromBase g))
        (F.map (Under.homMk (U := Under.mk f) (V := Under.mk (f ≫ i)) i rfl))
        (F.map (Under.homMk (U := Under.mk g) (V := Under.mk (f ≫ i)) j h.w.symm)))
    {n : ℕ} {s : Cocone (repeatedWideSpan f n)} (hs : IsColimit s) :
    IsColimit (mapRepeatedWideCocone F s) := by
  have H (n : ℕ) : ∃ t : Cocone (repeatedWideSpan f n),
      Nonempty (IsColimit t) ∧ Nonempty (IsColimit (mapRepeatedWideCocone F t)) := by
    induction n with
    | zero =>
      let t : Cocone (repeatedWideSpan f 0) :=
        WidePushoutShape.mkCocone (𝟙 X) (fun j ↦ Fin.elim0 j) (fun j ↦ Fin.elim0 j)
      have ht : IsColimit t := by
        refine ⟨fun s ↦ s.ι.app none, ?_, ?_⟩
        · intro s k
          rcases k with _ | j
          · exact Category.id_comp _
          · exact Fin.elim0 j
        · intro s k hk
          simpa [t] using hk none
      have hbase : (mapRepeatedWideCocone F t).ι.app none = 𝟙 _ := by
        change F.map (fromBase (𝟙 X)) = 𝟙 _
        rw [← F.map_id]
        congr 1
        exact (Under.mkIdInitial (X := X)).hom_ext _ _
      refine ⟨t, ⟨ht⟩, ⟨⟨fun s ↦ s.ι.app none, ?_, ?_⟩⟩⟩
      · intro s k
        rcases k with _ | j
        · rw [hbase, Category.id_comp]
        · exact Fin.elim0 j
      · intro s k hk
        simpa only [hbase, Category.id_comp] using hk none
    | succ n ih =>
      obtain ⟨t, ⟨ht⟩, ⟨hm⟩⟩ := ih
      let g := t.ι.app none
      letI := hex g
      let h := IsPushout.of_hasPushout f g
      let ht' := repeatedWideSpanSuccIsColimit ht h
      let hm' := repeatedWideSpanSuccIsColimit hm (hmap g _ _ h)
      refine ⟨_, ⟨ht'⟩, ⟨IsColimit.ofIsoColimit hm' (Cocone.ext (Iso.refl _) ?_)⟩⟩
      rintro (_ | k)
      · simp only [Iso.refl_hom, Category.comp_id]
        change F.map (fromBase f) ≫ F.map (Under.homMk _ rfl) = F.map (fromBase _)
        rw [← F.map_comp]
        congr 1
        exact (Under.mkIdInitial (X := X)).hom_ext _ _
      · refine Fin.cases ?_ (fun j ↦ ?_) k
        · simp only [Iso.refl_hom, Category.comp_id]
          rfl
        · simp only [Iso.refl_hom, Category.comp_id]
          change F.map (repeatedWideUnderLeg t j) ≫ F.map (Under.homMk (U := Under.mk g)
            (V := Under.mk (f ≫ pushout.inl f g)) (pushout.inr f g) h.w.symm) =
              F.map (Under.homMk (U := Under.mk f) (V := Under.mk (f ≫ pushout.inl f g)) _ _)
          rw [← F.map_comp]
          congr 1
  let ht := (H n).choose_spec.1.some
  let hmapt := (H n).choose_spec.2.some
  exact IsColimit.ofIsoColimit hmapt (mapRepeatedWideCoconeIso F (ht.uniqueUpToIso hs))

end CategoryTheory.Limits
