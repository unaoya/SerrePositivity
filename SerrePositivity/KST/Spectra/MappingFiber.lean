module

public import SerrePositivity.KST.Spectra.LoopFiber

/-!
概要：任意の点つき源からの Hom は点つき fiber を保存する。
方針：右随伴が kernel を保存することを使い、包含と可換な厳密同型を取る。
規約：Kan 性を要求しない。∞ 極限の主張は含めない。
使われ方：Goerss–Jardine I §7–8。path 内の fiber と fiber 内の path の比較。
-/

@[expose] public section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed

namespace SerrePositivity.KST.Spectra.PointedMapping

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：点つき Hom に送った fiber の kernel fork は極限。
方針：内部 Hom の右随伴性で、証明済みの kernel の極限性を移す。
規約：源 A は任意の点つき単体集合。
使われ方：Goerss–Jardine I §7。写像空間による fiber の保存。 -/
def fiberKernelIsLimit (A : PointedSimplicialSet.{u})
    {E B : PointedSimplicialSet.{u}} (p : E ⟶ B) :
    IsLimit ((pointedFiberKernelFork p).map (ihom A)) :=
  (pointedFiberKernelFork p).mapIsLimit (pointedFiberKernelIsLimit p) (ihom A)

/-- 概要：fiber への Hom と、Hom の後合成の fiber は点つき同型。
方針：同じ kernel の二つの極限の一意性を使う。
規約：通常の点つき圏の厳密な同型。
使われ方：Goerss–Jardine I §7–8。path と fiber の二方向の比較。 -/
def fiberIso (A : PointedSimplicialSet.{u}) {E B : PointedSimplicialSet.{u}} (p : E ⟶ B) :
    PointedObject.basedHom A (pointedFiber p) ≅
      pointedFiber (PointedObject.basedHomMap A p) :=
  (fiberKernelIsLimit A p).conePointUniqueUpToIso
    (pointedFiberKernelIsLimit (PointedObject.basedHomMap A p))

/-- 概要：Hom と fiber の比較同型は全空間への包含と可換。
方針：kernel の一意同型の射影への計算則を使う。
規約：同型の順方向。逆方向はこの等式から計算できる。
使われ方：Goerss–Jardine I §8。相対ホーンの面と path の終点を比較する。 -/
@[reassoc (attr := simp)]
lemma fiberIso_hom_ι (A : PointedSimplicialSet.{u})
    {E B : PointedSimplicialSet.{u}} (p : E ⟶ B) :
    (fiberIso A p).hom ≫ pointedFiberι (PointedObject.basedHomMap A p) =
      PointedObject.basedHomMap A (pointedFiberι p) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

/-- 概要：同型で fiber を戻してから包含すると Hom の元の射へ戻る。
方針：順方向の射影等式に逆同型を前合成する。
規約：写像族の代表を変更しない。
使われ方：Goerss–Jardine I §8。fiber 内の path の全空間での表示。 -/
@[reassoc (attr := simp)]
lemma fiberIso_inv_map_ι (A : PointedSimplicialSet.{u})
    {E B : PointedSimplicialSet.{u}} (p : E ⟶ B) :
    (fiberIso A p).inv ≫ PointedObject.basedHomMap A (pointedFiberι p) =
      pointedFiberι (PointedObject.basedHomMap A p) := by
  rw [← fiberIso_hom_ι, Iso.inv_hom_id_assoc]

end
end SerrePositivity.KST.Spectra.PointedMapping
