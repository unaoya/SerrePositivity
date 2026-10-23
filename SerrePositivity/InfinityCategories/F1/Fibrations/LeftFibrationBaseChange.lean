module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorPullbackLaws
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationMappingSpaces
public import SerrePositivity.InfinityCategories.F1.Coherent.NervePostcomposition

/-!
概要：left fibrations の豊穣的な底変換と coherent nerve 上の作用。
方針：通常の引き戻しと相対写像空間の底変換を豊穣関手にまとめる。
規約：全空間と底は宇宙 u、coherent nerve は u+1。∞ 極限は主張しない。
使われ方：Kerodon §5.3.1、Remark 5.6.2.5、straightening の底変換との整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：束縛した left fibration を指定した底の射に沿って引き戻す。
方針：引き戻しの第二射影に left fibration の底変換閉性を適用する。
規約：引き戻しの全空間の宇宙は元と同じ。
使われ方：Kerodon §5.3.1、底変換の対象への作用。 -/
noncomputable def leftFibrationBaseChangeObject {B D : SSet.{u}}
    (k : D ⟶ B) (p : LeftFibrationObject B) : LeftFibrationObject D :=
  ⟨Over.mk (pullback.snd p.val.hom k),
    ⟨leftFibrations.pullback_snd p.val.hom k (LeftFibration.mem (p := p.val.hom))⟩⟩

/-- 概要：底変換は left fibrations の単体的圏の豊穣関手。
方針：Hom の作用を相対写像空間の底変換とし、単位・合成の厳密な整合性を使う。
規約：底自体の quasicategory 性は要求しない。
使われ方：Kerodon §5.3.1、底変換の高次の写像族への作用。 -/
noncomputable def leftFibrationBaseChangeEnriched {B D : SSet.{u}} (k : D ⟶ B) :
    EnrichedFunctor SSet.{u} (LeftFibrationObject B) (LeftFibrationObject D) where
  obj := leftFibrationBaseChangeObject k
  map p q := relativeFunctorPullback p.val.hom q.val.hom k
  map_id p := relativeFunctorPullback_identity p.val k
  map_comp p q r := relativeFunctorPullback_composition p.val q.val r.val k

/-- 概要：底変換は left fibrations の coherent nerve の間の射を与える。
方針：底変換の豊穣関手へ coherent nerve の後合成を適用する。
規約：始域・終域はともに局所 Kan な単体的圏の coherent nerve。
使われ方：Kerodon Remark 5.6.2.5、分類の fibration 側の底変換関手。 -/
noncomputable def leftFibrationInfinityBaseChange {B D : SSet.{u}} (k : D ⟶ B) :
    LeftFibrationInfinity B ⟶ LeftFibrationInfinity D :=
  coherentNerveMap (leftFibrationBaseChangeEnriched k)

/-- 概要：coherent nerve 上の底変換は各対象を通常の引き戻しへ写す。
方針：coherent nerve の豊穣後合成の頂点公式を使う。
規約：対象の標準頂点での厳密な等式。
使われ方：Kerodon Remark 5.6.2.5、底変換関手の対象での同定。 -/
lemma leftFibrationInfinityBaseChange_vertex {B D : SSet.{u}}
    (k : D ⟶ B) (p : LeftFibrationObject B) :
    (leftFibrationInfinityBaseChange k).app (Opposite.op ⦋0⦌) (coherentNerveVertex p) =
      coherentNerveVertex (leftFibrationBaseChangeObject k p) :=
  coherentNerveMap_vertex (leftFibrationBaseChangeEnriched k) p

end SerrePositivity.InfinityCategories
