module

public import SerrePositivity.Archive.KST.DescentConditional.DisjointFamilyCechGeometry
public import SerrePositivity.Archive.KST.DescentConditional.FiniteFamilyCechFunctor
public import SerrePositivity.Archive.KST.DescentConditional.ConstantCechDescent

/-!
# 単射の被覆族から値の積への指定 Čech 比較

## 概要
単射の被覆族の Čech 図式から、各成分上の値の積の定数図式への自然な射を構成する。

## 方針
定数の添字の列への積射影と、構成済みの指定対角同型の逆を前層で写した射を合成する。

## 規約
単なる各次数の同型ではなく、単体射と元の指定増強の両方を保つ射を構成する。

## 使われ方
論文 公理 (1)、補題 3.2・3.3 の非交和被覆の実降下。
原典の τ 位相の層論を Čech 計算で置換する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w t z

open CategoryTheory CategoryTheory.Limits Opposite

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
  {ι : Type z} [Finite ι] {Y : C} (X : ι → C) (cover : ∀ i, X i ⟶ Y)
  [∀ i, Mono (cover i)] {V : Type w} [Category.{t} V] [HasFiniteProducts V]
  (F : Cᵒᵖ ⥤ V)

/-- 概要：各 Čech 段から各成分上の値の積への指定射（公理 (1)）。
方針：定数の添字の列の射影の後に、対角の引き戻しを適用する。
規約：元の値を積と先に同一視しない。使われ方：余単体の自然な比較。 -/
def familyCechDiagonalProjection (n : SimplexCategory) :
    familyCechValue X cover F n ⟶ ∏ᶜ fun i ↦ F.obj (op (X i)) :=
  Pi.lift fun i ↦
    Pi.π (fun a : Fin (n.len + 1) → ι ↦ F.obj (op (familyCechTerm X cover n a)))
      (fun _ ↦ i) ≫ F.map (familyCechDiagonalIso X cover n i).inv.op

/-- 概要：指定対角射影を定数図式への自然変換に束ねる（公理 (1)）。
方針：定数の添字の列の制限と幾何の対角の自然性を使う。
規約：全ての単体射で可換。使われ方：実際のホモトピー極限への比較。 -/
def familyCechDiagonalComparison : familyCechDiagram X cover F ⟶
    (Functor.const SimplexCategory).obj (∏ᶜ fun i ↦ F.obj (op (X i))) where
  app n := familyCechDiagonalProjection X cover F n
  naturality {n m} f := by
    apply Pi.hom_ext
    intro i
    have h := congrArg (fun q ↦ F.map q.op)
      (familyCechDiagonalIso_inv_naturality X cover f i)
    simp only [op_comp, F.map_comp] at h
    simpa [familyCechDiagonalProjection, familyCechDiagram, familyCechValueMap,
      Category.assoc] using
      congrArg (Pi.π
        (fun a : Fin (n.len + 1) → ι ↦ F.obj (op (familyCechTerm X cover n a)))
        (fun _ ↦ i) ≫ ·) h

/-- 概要：元の被覆射が指定する値の積への比較（公理 (1)）。
方針：各成分の制限写像を積の普遍性で束ねる。
規約：増強元上の指定射を固定。使われ方：非交和保存の実際の比較。 -/
def familyProductComparison : F.obj (op Y) ⟶ ∏ᶜ fun i ↦ F.obj (op (X i)) :=
  Pi.lift fun i ↦ F.map (cover i).op

/-- 概要：対角射影は元の増強から値の積への指定比較を保つ（公理 (1)）。
方針：各積射影で対角と基底射の合成を計算する。
規約：指定増強の全ての次数での可換性。使われ方：元の比較の弱同値の反映。 -/
theorem familyCechDiagonalComparison_augmentation (n : SimplexCategory) :
    (familyCechAugmentation X cover F).app n ≫
        (familyCechDiagonalComparison X cover F).app n =
      familyProductComparison X cover F := by
  apply Pi.hom_ext
  intro i
  simp [familyCechAugmentation, familyCechDiagonalComparison,
    familyCechDiagonalProjection, familyProductComparison,
    ← F.map_comp, ← op_comp, familyCechDiagonalIso]

/-- 概要：実際の被覆族 Čech から値の積の恒等増強への指定射（公理 (1)）。
方針：元の比較と全自然な対角射影を comma の射に束ねる。
規約：空間値の実際の増強つき図式。使われ方：公理 (1) から元の非交和の比較の弱同値を反映。 -/
def familyCechToConstantProduct (F : Cᵒᵖ ⥤ SSet.{0}) :
    familyCechSpace X cover F ⟶
      constantAugmentedCechSpace SimplexCategory (∏ᶜ fun i ↦ F.obj (op (X i))) where
  left := familyProductComparison X cover F
  right := familyCechDiagonalComparison X cover F
  w := by
    apply NatTrans.ext
    funext n
    change familyProductComparison X cover F ≫ 𝟙 _ =
      (familyCechAugmentation X cover F).app n ≫
        (familyCechDiagonalComparison X cover F).app n
    rw [Category.comp_id]
    exact (familyCechDiagonalComparison_augmentation X cover F n).symm

end SerrePositivity.KST.Descent
