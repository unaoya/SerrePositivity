module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordCutFactorMaps

/-!
# 元の切断因子の制限射の列回収と恒等・合成則

概要：prefix・残りへの制限は元の列の像を保ち、恒等射と合成を厳密に保持する。
方針：元の番号と残りの番号の減算を照合する。
規約：同じ元の語の射を使い、自然同型だけで置き換えない。
使われ方：切断因子の全語の図式の整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Word.CutFactor
open CategoryTheory

variable {a b c : Word} (f : a ⟶ b) (i : Fin a.length) (hi : a.direction i = .forward)

lemma prefixColumn_map (k : Fin (prefixWord a i).length) :
    prefixColumn b (f.orderHom i) ((prefixMap f i hi).orderHom k) =
      f.orderHom (prefixColumn a i k) := Fin.ext rfl

lemma residualColumn_map (k : Fin (residualWord a i).length) :
    residualColumn b (f.orderHom i) ((residualMap f i hi).orderHom k) =
      f.orderHom (residualColumn a i k) := by
  apply Fin.ext
  have hm := f.orderHom.monotone (le_residualColumn a i k)
  change (f.orderHom i).val +
    ((f.orderHom (residualColumn a i k)).val - (f.orderHom i).val) = _
  omega

lemma prefixMap_id : prefixMap (𝟙 a) i hi = 𝟙 (prefixWord a i) :=
  hom_ext _ _ (fun _ => Fin.ext rfl)

lemma residualMap_id : residualMap (𝟙 a) i hi = 𝟙 (residualWord a i) := by
  apply hom_ext
  intro k
  apply Fin.ext
  change i.val + k.val - i.val = k.val
  omega

lemma prefixMap_comp (g : b ⟶ c) :
    prefixMap (f ≫ g) i hi =
      prefixMap f i hi ≫ prefixMap g (f.orderHom i) ((f.direction_eq i).trans hi) :=
  hom_ext _ _ (fun _ => Fin.ext rfl)

lemma residualMap_comp (g : b ⟶ c) :
    residualMap (f ≫ g) i hi =
      residualMap f i hi ≫ residualMap g (f.orderHom i) ((f.direction_eq i).trans hi) := by
  apply hom_ext
  intro k
  apply Fin.ext
  change (g.orderHom (f.orderHom (residualColumn a i k))).val -
    (g.orderHom (f.orderHom i)).val =
    (g.orderHom (residualColumn b (f.orderHom i) ((residualMap f i hi).orderHom k))).val -
      (g.orderHom (f.orderHom i)).val
  rw [residualColumn_map]

lemma prefixMap_last : (prefixMap f i hi).orderHom (Fin.last i.val) =
    Fin.last (f.orderHom i).val := Fin.ext rfl

lemma residualMap_zero : (residualMap f i hi).orderHom
    (⟨0, by change 0 < 1 + (a.length - i.val - 1); omega⟩) =
      ⟨0, by change 0 < 1 + (b.length - (f.orderHom i).val - 1); omega⟩ := by
  apply Fin.ext
  exact Nat.sub_self _

end SerrePositivity.EInfinity.Hammock.Word.CutFactor
