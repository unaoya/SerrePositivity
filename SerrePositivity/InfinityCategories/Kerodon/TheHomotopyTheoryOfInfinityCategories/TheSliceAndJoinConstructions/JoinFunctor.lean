module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinAnodyne
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
概要：左因子を固定した join 関手と部分複体の貼り合わせ。
方針：joinMap の関手性と補った次数での所属条件から交わりと和を計算する。
規約：join の直接定義を維持し、Day 畳み込みは使わない。
使われ方：HTT §1.2.8・1.2.13、Kerodon §7.1（Tag 02H1） の cospan の錐と正方形。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits SSet
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：左因子を固定した join は単体集合の関手。
方針：右因子の射を joinMap で写す。
規約：左因子 A の射は恒等。
使われ方：HTT §1.2.8、Kerodon §4.3.5（Tag 017V） の join と同型・貼り合わせ。 -/
def joinRightFunctor (A : SSet.{u}) : SSet.{u} ⥤ SSet.{u} where
  obj B := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B
  map f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 A) f
  map_id B := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_id A B
  map_comp f g := by simpa only [Category.id_comp] using _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp (𝟙 A) (𝟙 A) f g

/-- 概要：補った次数で交わりに属することは両方に属すること。
方針：空区間と非空区間に分ける。
規約：空区間では全ての所属条件が真。
使われ方：HTT §1.2.8、Kerodon §4.3.5（Tag 017V） の join の交わり。 -/
lemma Join.augMem_inf {B : SSet.{u}} (B₀ B₁ : B.Subcomplex) (r : ℕ) (b : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj B r) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.augMem (B₀ ⊓ B₁) r b ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.augMem B₀ r b ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.augMem B₁ r b := by
  cases r <;> simp [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.augMem]

/-- 概要：補った次数で和に属することはいずれかに属すること。
方針：空区間と非空区間に分ける。
規約：空区間では全ての所属条件が真。
使われ方：HTT §1.2.8、Kerodon §4.3.5（Tag 017V） の join の和。 -/
lemma Join.augMem_sup {B : SSet.{u}} (B₀ B₁ : B.Subcomplex) (r : ℕ) (b : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj B r) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.augMem (B₀ ⊔ B₁) r b ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.augMem B₀ r b ∨ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.augMem B₁ r b := by
  cases r <;> simp [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.augMem]

/-- 概要：右因子の部分複体の交わりは join の交わりに写る。
方針：切断位置ごとの右単体の所属を計算する。
規約：左因子は共通に固定する。
使われ方：HTT §1.2.8、Kerodon §4.3.5（Tag 017V） の join による貼り合わせ。 -/
lemma joinSubcomplexRight_inf (A : SSet.{u}) {B : SSet.{u}} (B₀ B₁ : B.Subcomplex) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexRight A (B₀ ⊓ B₁) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexRight A B₀ ⊓ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexRight A B₁ := by
  ext ⟨⟨n⟩⟩ s
  change (s ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexRight A (B₀ ⊓ B₁)).obj (Opposite.op ⦋n⦌)) ↔
    s ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexRight A B₀).obj (Opposite.op ⦋n⦌) ∧
    s ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexRight A B₁).obj (Opposite.op ⦋n⦌)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.mem_joinSubcomplexRight, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.mem_joinSubcomplexRight,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.mem_joinSubcomplexRight, Join.augMem_inf]

/-- 概要：右因子の二つの部分複体の和は join の和に写る。
方針：切断位置ごとの右単体の所属を計算する。
規約：二項の和であり、空族の和の保存は主張しない。
使われ方：HTT §1.2.8、Kerodon §4.3.5（Tag 017V） の join による貼り合わせ。 -/
lemma joinSubcomplexRight_sup (A : SSet.{u}) {B : SSet.{u}} (B₀ B₁ : B.Subcomplex) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexRight A (B₀ ⊔ B₁) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexRight A B₀ ⊔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexRight A B₁ := by
  ext ⟨⟨n⟩⟩ s
  change (s ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexRight A (B₀ ⊔ B₁)).obj (Opposite.op ⦋n⦌)) ↔
    s ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexRight A B₀).obj (Opposite.op ⦋n⦌) ∨
    s ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexRight A B₁).obj (Opposite.op ⦋n⦌)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.mem_joinSubcomplexRight, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.mem_joinSubcomplexRight,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.mem_joinSubcomplexRight, Join.augMem_sup]

/-- 概要：右因子の部分複体の双カルテジアン正方形は join の双カルテジアン正方形に写る。
方針：二項の交わりと和の保存を使う。
規約：左因子を固定する。
使われ方：HTT §1.2.8、Kerodon §7.1（Tag 02H1） の cospan の錐の二三角形への分解。 -/
lemma joinSubcomplexRight_bicartSq (A : SSet.{u}) {B : SSet.{u}}
    {B₀ B₁ B₂ B₃ : B.Subcomplex} (h : Subcomplex.BicartSq B₀ B₁ B₂ B₃) :
    Subcomplex.BicartSq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexRight A B₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexRight A B₁)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexRight A B₂) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexRight A B₃) where
  sup_eq := by rw [← joinSubcomplexRight_sup, h.sup_eq]
  inf_eq := by rw [← joinSubcomplexRight_inf, h.inf_eq]

/-- 概要：右因子の部分複体の表示同型から、その join の像への同型を作る。
方針：join 関手で同型を写し、単射の像との同型を合成する。
規約：表示同型の向きは C から部分複体へ。
使われ方：HTT §1.2.8、Kerodon §7.1（Tag 02H1） の標準単体での pushout の表示。 -/
noncomputable def joinRightSubcomplexIso (A : SSet.{u}) {B C : SSet.{u}}
    (B₀ : B.Subcomplex) (e : C ≅ (B₀ : SSet.{u})) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A C ≅ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexRight A B₀ : SSet.{u}) :=
  (joinRightFunctor A).mapIso e ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexRightIso A B₀

/-- 概要：右因子の部分複体の表示同型と join の周囲への包含は可換。
方針：像との同型の包含式と joinMap の合成則を使う。
規約：右因子では表示同型の後に部分複体の包含を適用する。
使われ方：HTT §1.2.8、Kerodon §7.1（Tag 02H1） の pushout の比較。 -/
lemma joinRightSubcomplexIso_hom_ι (A : SSet.{u}) {B C : SSet.{u}}
    (B₀ : B.Subcomplex) (e : C ≅ (B₀ : SSet.{u})) :
    (joinRightSubcomplexIso A B₀ e).hom ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexRight A B₀).ι =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 A) (e.hom ≫ B₀.ι) := by
  rw [joinRightSubcomplexIso, Iso.trans_hom, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexRightIso_hom_ι]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 A) e.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 A) B₀.ι = _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp]

/-- 概要：cospan のホーンとの join は二つの辺との join を共通の点との join で貼った pushout。
方針：ホーンの部分複体の双カルテジアン正方形を join に写し、面の表示同型を使う。
規約：ホーンは Λ[2,2]、共通の点は最後の頂点。
使われ方：HTT §1.2.13、Kerodon §7.1（Tag 02H1） の引き戻しの錐。 -/
lemma joinRight_horn₂₂_isPushout (A : SSet.{u}) :
    IsPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 A) (stdSimplex.δ (0 : Fin 2)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 A) (stdSimplex.δ (0 : Fin 2)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 A) horn₂₂.ι₀₂) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 A) horn₂₂.ι₁₂) := by
  let hs := joinSubcomplexRight_bicartSq A horn₂₂.sq
  apply hs.isPushout.of_iso'
    (joinRightSubcomplexIso A (stdSimplex.face {2}) (stdSimplex.faceSingletonIso 2))
    (joinRightSubcomplexIso A (stdSimplex.face {0, 2}) (stdSimplex.facePairIso 0 2 (by decide)))
    (joinRightSubcomplexIso A (stdSimplex.face {1, 2}) (stdSimplex.facePairIso 1 2 (by decide)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexRightIso A (horn 2 2))
  · apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexRight A (stdSimplex.face {0, 2})).ι).1
    simp only [Category.assoc, Subcomplex.homOfLE_ι, joinRightSubcomplexIso_hom_ι]
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp]
    apply congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 A))
    apply SSet.yonedaEquiv.injective
    decide
  · apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexRight A (stdSimplex.face {1, 2})).ι).1
    simp only [Category.assoc, Subcomplex.homOfLE_ι, joinRightSubcomplexIso_hom_ι]
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp]
    apply congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 A))
    apply SSet.yonedaEquiv.injective
    decide
  · apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexRight A (horn 2 2)).ι).1
    simp only [Category.assoc, Subcomplex.homOfLE_ι, joinRightSubcomplexIso_hom_ι,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexRightIso_hom_ι]
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp]
    apply congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 A))
    apply SSet.yonedaEquiv.injective
    decide
  · apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexRight A (horn 2 2)).ι).1
    simp only [Category.assoc, Subcomplex.homOfLE_ι, joinRightSubcomplexIso_hom_ι,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexRightIso_hom_ι]
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp]
    apply congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 A))
    apply SSet.yonedaEquiv.injective
    decide

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
