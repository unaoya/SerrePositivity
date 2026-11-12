module

public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.SkeletalAttachmentPushout
public import SerrePositivity.KST.Spectra.PointedCofiberPushout
public import SerrePositivity.KST.Spectra.SkeletalMappingFiber

/-!
概要：骨格の相対 cofiber を境界包含の余積の cofiber と同定する。
方針：骨格のセルを貼る pushout に自由基点を加え、対向する cofiber を比較する。
規約：通常の cofiber の点つき同型。段 n の追加セルは次元 n+1。
使われ方：Goerss–Jardine VIII §1。塔の fiber を個々の単体の写像空間で計算する準備。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance skeletalCofiberAdjoinLeftAdjoint :
    (PointedObject.adjoinFunctor (C := SSet.{u})).IsLeftAdjoint :=
  PointedObject.adjoinForgetAdjunction.isLeftAdjoint

/-- 概要：d 単体の境界包含の余積を潰した点つき cofiber。
方針：境界包含の余積に自由基点を加えて cofiber を取る。
規約：添字は d 次元のセルであり cellEquiv で非退化単体へ移せる。
使われ方：Goerss–Jardine VIII §1。fiber のセルごとの表示の源。 -/
def cellCofiber (K : SSet.{u}) (d : ℕ) : PointedSimplicialSet.{u} :=
  pointedCofiber (PointedObject.adjoinFunctor.map
    (SSet.relativeCellComplexOfMono.l (K.skeleton d).ι d))

/-- 概要：相対骨格の cofiber は境界包含の余積の cofiber と同型。
方針：自由基点追加が保存するセルの pushout に cofiber の比較を適用する。
規約：この同型は同倫同値より強い厳密な点つき同型。
使われ方：Goerss–Jardine VIII §1。塔の fiber の源のセル分解。 -/
def relativeCofiberIso (K : SSet.{u}) (d : ℕ) :
    pointedCofiber (PointedObject.adjoinFunctor.map
      (Subcomplex.homOfLE (K.skeleton.monotone (Nat.le_succ d)))) ≅ cellCofiber K d :=
  pointedCofiberPushoutIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.isPushout K d).map PointedObject.adjoinFunctor)

/-- 概要：骨格の写像空間の各 fiber をセルの境界の余積の cofiber で表示する。
方針：源の cofiber の同型を内部 Hom へ反変に送り、既存の fiber 同型に合成する。
規約：係数の Kan 性はこの厳密な同型には不要。
使われ方：Goerss–Jardine VIII §1。各 fiber の群をセルの寄与へ分ける界面。 -/
def stageFiberCellIso (K : SSet.{u}) (X : PointedSimplicialSet.{u}) (n : ℕ) :
    PointedObject.basedHom (cellCofiber K (n + 1)) X ≅
      UnbasedPointedMapping.stageFiber K X n :=
  (internalHom.flip.obj X).mapIso (relativeCofiberIso K (n + 1)).op ≪≫
    UnbasedPointedMapping.stageFiberIso K X n

end

end SerrePositivity.KST.Spectra.SkeletalCellAttachment
