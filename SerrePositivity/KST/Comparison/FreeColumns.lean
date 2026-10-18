module

public import SerrePositivity.KST.Comparison.FreeDegeneraciesEquivalence

/-!
# 二重単体集合の各列の自由な退化

概要：各列に自由な退化を付け、fat realization と同じ次数ごとの標準形を得る。
方針：二重単体集合を転置し、自由な退化を後合成する。
規約：Segal 1974 Proposition 1.6 の模型比較の補助。
使われ方：fat realization を列の自由な退化の対角と同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite
open SerrePositivity.BisimplicialModel

/--
概要：二重単体集合の各列に自由な退化を付けた図式。
方針：転置した後で自由な退化の関手を後合成する。
規約：外側の添字は元の内側の次数。
使われ方：fat realization と対角の比較の中間対象。
-/
def freeColumns (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) : SimplexCategoryᵒᵖ ⥤ SSet.{u} :=
  F.flip ⋙ freeDegeneracies

/--
概要：各列の自由な退化から転置した元の図式への augmentation。
方針：自由な退化の自然な augmentation を各列で評価する。
規約：この自然変換は各行で局所化同型である。
使われ方：対角の局所化同型保存への入力。
-/
def freeColumnsAugmentation (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) : freeColumns F ⟶ F.flip :=
  Functor.whiskerLeft F.flip freeDegeneraciesAugmentation

/--
概要：二重単体集合を転置しても対角は自然に同型である。
方針：各次数で恒等写像を取り、二つの作用の交換を自然性から確認する。
規約：二つの次数の単体作用の順序だけを交換する。
使われ方：各列の augmentation の対角を元の対角へ戻す。
-/
def diagonalFlipIso (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) : diagonal.obj F.flip ≅ diagonal.obj F :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun θ => by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg (fun t => t x) ((F.map θ).naturality θ))

/--
概要：fat realization と列の自由な退化は各次数で同じ全射の標準形を持つ。
方針：全射と中間次数と行の元をそのまま対応させる。
規約：元の二重単体集合の二つの評価の順序を変えるだけ。
使われ方：二つの実際の模型の同型の各次数の成分。
-/
def fatColumnNormalFormEquiv (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (d : SimplexCategoryᵒᵖ) :
    FatNormalForm F d ≃ FatNormalForm (discreteRowsFunctor.obj (F.flip.obj d)) d where
  toFun p := ⟨p.degree, p.epi, p.epi_property, p.simplex⟩
  invFun p := ⟨p.degree, p.epi, p.epi_property, p.simplex⟩
  left_inv _ := rfl
  right_inv _ := rfl

/--
概要：fat realization の各次数と列の自由な退化の対角の次数との同型。
方針：両方の標準形の同値を合成する。
規約：単体作用との整合は別途証明する。
使われ方：模型の同型の成分。
-/
def fatFreeColumnsDegreeIso (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (d : SimplexCategoryᵒᵖ) :
    (fatRealization F).obj d ≅ (diagonal.obj (freeColumns F)).obj d :=
  Equiv.toIso ((fatNormalFormEquiv F d).trans
    ((fatColumnNormalFormEquiv F d).trans (freeDegeneraciesNormalForm (F.flip.obj d) d).symm))

end SerrePositivity.KST.Comparison
