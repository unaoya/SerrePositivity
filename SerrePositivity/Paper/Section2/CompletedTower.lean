module

public import SerrePositivity.LengthAlgebra.RootTowerLength.Completion
public import SerrePositivity.Paper.Section2.TowerLengthOn
public import SerrePositivity.CommutativeAlgebra.RootTower.Koszul

/-! # 根の塔の完備化上の長さと Koszul の冪ねじれ

完備化の環・標準写像・拡大イデアルの定義は
`CommutativeAlgebra/RootTower/Completion.lean` に抽出した。
長さの係数制限の比較をこのファイルで扱い、有限局所包含に対する
Koszul ホモロジーの冪ねじれは `RootTower/Koszul.lean` を再公開する。
長さの加法性も共通層で証明済みであり、純粋な完備化の環の定義とは分離している。
-/

@[expose] public section
universe u
open IsLocalRing
namespace SerrePositivity.Section2

variable (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ)
    [IsLocalRing A] [IsNoetherianRing A] [Fact p.Prime] (ht : ∀ i, t i ∈ maximalIdeal A)

/-- 完備化上の正規化長さ：非完備な塔に制限して測る。 -/
noncomputable def completedTowerLength :
    NormalizedLength (CompletedTower A t p) (completedTowerMaxIdeal A t p) :=
  RootTowerLength.completedNormalizedLength A t p ht

variable (D : Type u) [CommRing D] [IsLocalRing D] [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D))
    (C : Type u) [CommRing C] [Algebra A C] [Algebra D C]
    [Algebra (Tower A t p) C] [Algebra (CompletedTower A t p) C]
    [IsScalarTower A D C] [IsScalarTower A (Tower A t p) C]
    [IsScalarTower A (CompletedTower A t p) C]
    [IsScalarTower (Tower A t p) (CompletedTower A t p) C]

omit [IsScalarTower A (CompletedTower A t p) C] in
/-- 完備化を経由して係数を制限しても、長さ代数の長さは変わらない。 -/
theorem towerLengthOn_eq_completedTowerLength
    (M : Type u) [AddCommGroup M] [Module C M] :
    (towerLengthOn A D hinj t p ht C).len M =
      (letI := Module.compHom M (algebraMap (CompletedTower A t p) C)
       (completedTowerLength A t p ht).len M) := by
  exact completedLengthOf_restrictScalars A t p (towerLength A t p ht) C M

end SerrePositivity.Section2
