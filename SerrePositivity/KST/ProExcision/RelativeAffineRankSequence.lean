module
public import SerrePositivity.KST.ProExcision.SimplicialColumnBlockInclusion
public import SerrePositivity.KST.ProExcision.SequentialModuleRepresentatives
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# 有限 rank の相対アフィン加群の実順序余極限

概要：通常のブロック安定化が誘導する相対 bar 加群の列を実際に構成する。
方針：実対射の相対写像を順序列にし、ModuleCat の余極限を取る。
規約：KST Proposition 4.14。安定 H_* との比較は H_* 所有レーンの界面であり、この定義と区別する。
使われ方：有限 rank の相対零化を余極限へ移す代数部分。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Limits

/-- 概要：通常の安定化による有限 rank の相対 bar 加群の順序列。
方針：基底の単位ブロック和と列の零埋めの実対射を関手 F で相対項へ降ろす。
規約：KST Proposition 4.14、F は明示的に借用する関手。
使われ方：有限 rank の相対写像を安定化する実図式。 -/
def NonUnitalSimplicialRing.relativeAffineRankSequence (I : NonUnitalSimplicialRing.{u})
    (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) : ℕ ⥤ ModuleCat.{u} ℤ :=
  Functor.ofSequence (fun n ↦ relativeBarPairMap F (I.columnBlockOverHom n 1).toPairMap)

/-- 概要：有限 rank の相対アフィン加群の実余極限。
方針：ModuleCat の順序余極限を使う。
規約：KST Proposition 4.14、安定 H_* との模型同定そのものは主張しない。
使われ方：有限 rank の代表を使う零化の移送。 -/
def NonUnitalSimplicialRing.relativeAffineColimit (I : NonUnitalSimplicialRing.{u})
    (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) : ModuleCat.{u} ℤ :=
  colimit (I.relativeAffineRankSequence F)

/-- 概要：有限 rank の相対アフィン加群から実余極限への脚。
方針：実余極限の標準脚を使う。
規約：KST Proposition 4.14。使われ方：安定化の有限 rank の代表。 -/
def NonUnitalSimplicialRing.relativeAffineInclusion (I : NonUnitalSimplicialRing.{u})
    (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) (n : ℕ) :
    relativeBarModule F (I.hatGLColumnAction n) ⟶ I.relativeAffineColimit F :=
  colimit.ι (I.relativeAffineRankSequence F) n

/-- 概要：有限 rank の相対アフィン加群の実余極限の各元は有限 rank に由来する。
方針：実加群余極限の有限段階の代表の定理を適用する。
規約：KST Claim 4.15 から安定化への代数部分。
使われ方：零化の rank を代表元ごとに選ぶ。 -/
lemma NonUnitalSimplicialRing.relativeAffine_representative (I : NonUnitalSimplicialRing.{u})
    (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) (x : I.relativeAffineColimit F) :
    ∃ n, ∃ v : relativeBarModule F (I.hatGLColumnAction n), (I.relativeAffineInclusion F n).hom v = x :=
  sequentialModule_representative (I.relativeAffineRankSequence F) _
    (colimit.isColimit (I.relativeAffineRankSequence F)) x

end SerrePositivity.KST.ProExcision
