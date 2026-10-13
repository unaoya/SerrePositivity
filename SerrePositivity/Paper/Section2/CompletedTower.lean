module

public import SerrePositivity.LengthAlgebra.RootTowerLength.Completion
public import SerrePositivity.Paper.Section2.TowerLengthOn
public import SerrePositivity.CommutativeAlgebra.RootTower.Koszul

/-! # 根の塔の完備化上の長さと Koszul の冪ねじれ

完備化の環・標準写像・拡大イデアルの定義は
`CommutativeAlgebra/RootTower/Completion.lean` に抽出した。
長さの係数制限の比較をこのファイルで扱い、有限局所包含に対する
Koszul ホモロジーの冪ねじれは `RootTower/Koszul.lean` を再公開する。
既存の長さの引用依存は残るが、純粋な完備化の共通層には持ち込まない。
-/

@[expose] public section
universe u
open IsLocalRing
namespace SerrePositivity.Section2

variable (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ)
    [IsLocalRing A]

/-- 完備化上の正規化長さ：非完備な塔に制限して測る。 -/
noncomputable def completedTowerLength :
    NormalizedLength (CompletedTower A t p) (completedTowerMaxIdeal A t p) :=
  completedLengthOf A t p (towerLength A t p)

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
    (towerLengthOn A D hinj t p C).len M =
      (letI := Module.compHom M (algebraMap (CompletedTower A t p) C)
       (completedTowerLength A t p).len M) := by
  exact completedLengthOf_restrictScalars A t p (towerLength A t p) C M

end SerrePositivity.Section2
