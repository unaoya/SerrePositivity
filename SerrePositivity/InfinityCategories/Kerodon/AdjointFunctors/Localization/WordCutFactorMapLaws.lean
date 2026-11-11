module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps

/-!
# 元の切断因子の制限射の列回収と恒等・合成則

概要：prefix・残りへの制限は元の列の像を保ち、恒等射と合成を厳密に保持する。
方針：元の番号と残りの番号の減算を照合する。
規約：同じ元の語の射を使い、自然同型だけで置き換えない。
使われ方：切断因子の全語の図式の整合。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {a b c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) (i : Fin a.length) (hi : a.direction i = .forward)

lemma prefixColumn_map (k : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixWord a i).length) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixColumn b (f.orderHom i) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.prefixMap f i hi).orderHom k) =
      f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixColumn a i k) := Fin.ext rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.CutFactor.prefixColumn_map export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (prefixColumn_map)


lemma residualColumn_map (k : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualWord a i).length) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualColumn b (f.orderHom i) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.residualMap f i hi).orderHom k) =
      f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualColumn a i k) := by
  apply Fin.ext
  have hm := f.orderHom.monotone (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.le_residualColumn a i k)
  change (f.orderHom i).val +
    ((f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualColumn a i k)).val - (f.orderHom i).val) = _
  omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.CutFactor.residualColumn_map export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (residualColumn_map)


lemma prefixMap_id : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.prefixMap (𝟙 a) i hi = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixWord a i) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.hom_ext _ _ (fun _ => Fin.ext rfl)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.CutFactor.prefixMap_id export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (prefixMap_id)


lemma residualMap_id : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.residualMap (𝟙 a) i hi = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualWord a i) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.hom_ext
  intro k
  apply Fin.ext
  change i.val + k.val - i.val = k.val
  omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.CutFactor.residualMap_id export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (residualMap_id)


lemma prefixMap_comp (g : b ⟶ c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.prefixMap (f ≫ g) i hi =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.prefixMap f i hi ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.prefixMap g (f.orderHom i) ((f.direction_eq i).trans hi) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.hom_ext _ _ (fun _ => Fin.ext rfl)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.CutFactor.prefixMap_comp export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (prefixMap_comp)


lemma residualMap_comp (g : b ⟶ c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.residualMap (f ≫ g) i hi =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.residualMap f i hi ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.residualMap g (f.orderHom i) ((f.direction_eq i).trans hi) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.hom_ext
  intro k
  apply Fin.ext
  change (g.orderHom (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualColumn a i k))).val -
    (g.orderHom (f.orderHom i)).val =
    (g.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualColumn b (f.orderHom i) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.residualMap f i hi).orderHom k))).val -
      (g.orderHom (f.orderHom i)).val
  rw [residualColumn_map]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.CutFactor.residualMap_comp export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (residualMap_comp)


lemma prefixMap_last : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.prefixMap f i hi).orderHom (Fin.last i.val) =
    Fin.last (f.orderHom i).val := Fin.ext rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.CutFactor.prefixMap_last export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (prefixMap_last)


lemma residualMap_zero : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.residualMap f i hi).orderHom
    (⟨0, by change 0 < 1 + (a.length - i.val - 1); omega⟩) =
      ⟨0, by change 0 < 1 + (b.length - (f.orderHom i).val - 1); omega⟩ := by
  apply Fin.ext
  exact Nat.sub_self _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.CutFactor.residualMap_zero export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (residualMap_zero)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
