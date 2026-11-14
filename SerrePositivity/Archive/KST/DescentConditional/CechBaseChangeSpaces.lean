module

public import SerrePositivity.KST.Descent.CechBaseChangeOver
public import SerrePositivity.Archive.KST.DescentConditional.PresheafCechSpaces
public import SerrePositivity.Archive.KST.DescentConditional.SplitCechDescent

/-!
# 底変換 Čech の指定空間図式との接続

## 概要
前層の transfer に使う底変換図式を、実際の底変換被覆の指定 Čech 空間図式へ同定する。

## 方針
既存の基底・全段・増強の幾何同型を同じ値域関手で写し、増強を保持する comma 同型にする。

## 規約
余単体添字は元の単体圏を使う。二重反対圏は指定の前合成で除く。

## 使われ方
論文 補題 3.2 の有限平坦 transfer と証明済みの分裂降下の接続。
-/

@[expose] public section

noncomputable section

universe u v w t

open CategoryTheory CategoryTheory.Limits Opposite

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] {V : Type w} [Category.{t} V]
  {K : Type} [SmallCategory K] {Y : C} (D : Kᵒᵖ ⥤ Over Y) (U : V ⥤ SSet.{0})

/-- 概要：元の余単体添字での前層の指定増強つき空間図式（補題 3.2）。
方針：既存の全自然な関手に二重反対圏の指定添字を前合成する。
規約：元の前層と値域関手を全ての射で保つ。使われ方：transfer retract の実際の移送。 -/
def presheafCosimplicialSpaces : ((Over Y)ᵒᵖ ⥤ V) ⥤ AugmentedCechDiagram K :=
  presheafAugmentedCechSpaces D U ⋙ CechReindex.augmentedRestriction (opOp K)

variable [HasFiniteLimits C] {W X : C} (cover : W ⟶ Y) (f : X ⟶ Y)

/-- 概要：元の前層を基底上に制限した指定図式は元の Čech 空間図式と同型（補題 3.2）。
方針：元の幾何的増強と関手が保つ恒等射を成分で比較する。
規約：増強元は元の基底での前層の値。使われ方：元の Čech への transfer の結論。 -/
def cechOverPresheafSpaceIso (F : Cᵒᵖ ⥤ V) :
    (presheafCosimplicialSpaces (cechOverDiagram cover) U).obj
        (overPresheaf (Y := Y) F) ≅ cechAugmentedPresheafSpace cover (F ⋙ U) :=
  Comma.isoMk (Iso.refl _) (Iso.refl _) (by
    apply NatTrans.ext
    funext n
    exact (Category.id_comp _).trans (Category.comp_id _).symm)

/-- 概要：底変換前層の指定図式と実際の底変換被覆の Čech 空間図式は同型（補題 3.2）。
方針：指定基底同型と全段の同型を値域関手で写し、既存の増強の可換式を保持する。
規約：同じ元の前層を使う。使われ方：証明済みの分裂降下を transfer の比較先へ移す。 -/
def cechBaseChangedPresheafSpaceIso (F : Cᵒᵖ ⥤ V) :
    (presheafCosimplicialSpaces (cechOverDiagram cover) U).obj (baseChangedPresheaf f F) ≅
      cechAugmentedPresheafSpace (pullback.snd cover f) (F ⋙ U) :=
  Comma.isoMk
    (U.mapIso (F.mapIso (Iso.op (((Over.forget Y).mapIso (overBaseChangeBaseIso f)).symm))))
    (Functor.isoWhiskerLeft (opOp SimplexCategory)
      (Functor.isoWhiskerRight (cechBaseChangePresheafIso cover f F) U)) (by
      apply NatTrans.ext
      funext n
      have hw := congrArg (fun t ↦ t.app (op (op n)))
        (cechBaseChangeAugmentationIso cover f F).hom.w
      change F.map (overBaseChangeBaseIso f).inv.left.op ≫
          F.map ((Arrow.mk (pullback.snd cover f)).augmentedCechNerve.hom.app (op n)).op =
        F.map (((overBaseChange f).map
          (overDiagramToBase (cechOverDiagram cover) (op n))).left).op ≫
          F.map (cechBaseChangeStageIso cover f (op n)).hom.op at hw
      change U.map (F.map (overBaseChangeBaseIso f).inv.left.op) ≫
          (𝟙 _ ≫ U.map (F.map
            ((Arrow.mk (pullback.snd cover f)).augmentedCechNerve.hom.app (op n)).op)) =
        U.map (F.map (((overBaseChange f).map
          (overDiagramToBase (cechOverDiagram cover) (op n))).left).op) ≫
          U.map (F.map (cechBaseChangeStageIso cover f (op n)).hom.op)
      exact (congrArg (_ ≫ ·) (Category.id_comp _)).trans
        ((U.map_comp _ _).symm.trans ((congrArg U.map hw).trans (U.map_comp _ _))))

end SerrePositivity.KST.Descent
