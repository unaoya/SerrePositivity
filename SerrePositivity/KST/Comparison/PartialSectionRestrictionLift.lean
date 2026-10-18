module

public import SerrePositivity.KST.Comparison.PartialSectionAdjunct
public import SerrePositivity.KST.Comparison.MonoBasePullback

/-!
# 単射上の部分切断から元の全空間への復元

概要：A→B を経由する対象上の部分切断を、元の Z→A への写像に戻す。
方針：部分切断を随伴で戻し、T×_B A≅T の逆を前合成する。
規約：Segal 1974 Lemma 1.7 の単射に沿う trivial fibration の延長の制限。
使われ方：部分切断の包含が厳密な引き戻しとなることの普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits

/--
概要：単射を経由する対象上の部分切断から、元の全空間への射を復元する。
方針：基底変換の標準同型の逆と、随伴で戻した切断を合成する。
規約：r は s≫p を基底射に持つ B 上の射。
使われ方：制限の引き戻しへの持ち上げ。
-/
def partialSectionRestrictionLift {Z A B T : SSet.{u}} (p : A ⟶ B) [Mono p]
    (q : Z ⟶ A) (s : T ⟶ A) (r : Over.mk (s ≫ p) ⟶ partialSectionObject p q) : T ⟶ Z :=
  (monoBasePullbackIso p s).inv ≫ partialSectionAdjunct p q r

/--
概要：復元した射は指定された A への射を持ち上げる。
方針：随伴で戻した切断の基底条件と、引き戻し同型の第二射影を使う。
規約：trivial fibration 性は不要。
使われ方：制限の引き戻し正方形の第二成分。
-/
@[reassoc] theorem partialSectionRestrictionLift_comp {Z A B T : SSet.{u}}
    (p : A ⟶ B) [Mono p] (q : Z ⟶ A) (s : T ⟶ A)
    (r : Over.mk (s ≫ p) ⟶ partialSectionObject p q) :
    partialSectionRestrictionLift p q s r ≫ q = s := by
  change ((monoBasePullbackIso p s).inv ≫ partialSectionAdjunct p q r) ≫ q = s
  rw [Category.assoc, partialSectionAdjunct_comp]
  exact monoBasePullbackIso_inv_snd p s

/--
概要：復元した射を B 上の射として表す。
方針：A 上の整合を B へ後合成する。
規約：元の全空間の基底射は q≫p。
使われ方：部分切断の包含との合成の比較。
-/
def partialSectionRestrictionLiftOver {Z A B T : SSet.{u}} (p : A ⟶ B) [Mono p]
    (q : Z ⟶ A) (s : T ⟶ A) (r : Over.mk (s ≫ p) ⟶ partialSectionObject p q) :
    Over.mk (s ≫ p) ⟶ Over.mk (q ≫ p) :=
  Over.homMk (partialSectionRestrictionLift p q s r) (by
    change partialSectionRestrictionLift p q s r ≫ (q ≫ p) = s ≫ p
    rw [← Category.assoc, partialSectionRestrictionLift_comp])

/--
概要：復元した射を部分切断の対象へ戻すと、元の B 上の部分切断に一致する。
方針：随伴表示で比較し、第一射影と標準同型の逆の合成を打ち消す。
規約：等式は B 上の射として厳密に成立する。
使われ方：制限の引き戻しの第一成分の等式。
-/
theorem partialSectionRestrictionLiftOver_inclusion {Z A B T : SSet.{u}}
    (p : A ⟶ B) [Mono p] (q : Z ⟶ A) (s : T ⟶ A)
    (r : Over.mk (s ≫ p) ⟶ partialSectionObject p q) :
    partialSectionRestrictionLiftOver p q s r ≫ partialSectionInclusionOver p q = r := by
  apply partialSection_hom_ext p q
  rw [partialSectionAdjunct_naturality, partialSectionAdjunct_inclusion]
  have hmap : (sliceFiberFunctor p).map (partialSectionRestrictionLiftOver p q s r) ≫
      pullback.fst (q ≫ p) p =
    pullback.fst (s ≫ p) p ≫ partialSectionRestrictionLift p q s r :=
    sliceFiberFunctor_map_fst p (partialSectionRestrictionLiftOver p q s r)
  rw [hmap]
  change (monoBasePullbackIso p s).hom ≫
    ((monoBasePullbackIso p s).inv ≫ partialSectionAdjunct p q r) = partialSectionAdjunct p q r
  exact Iso.hom_inv_id_assoc _ _

/--
概要：復元した射と包含の合成は、元の部分切断の基礎写像に一致する。
方針：B 上の等式を忘却する。
規約：この等式と A への基底条件が引き戻しの二条件。
使われ方：延長を制限する引き戻しの普遍性。
-/
@[reassoc] theorem partialSectionRestrictionLift_inclusion {Z A B T : SSet.{u}}
    (p : A ⟶ B) [Mono p] (q : Z ⟶ A) (s : T ⟶ A)
    (r : Over.mk (s ≫ p) ⟶ partialSectionObject p q) :
    partialSectionRestrictionLift p q s r ≫ partialSectionInclusion p q = r.left :=
  congrArg (fun f => f.left) (partialSectionRestrictionLiftOver_inclusion p q s r)

/--
概要：基底条件と部分切断への合成で指定された元の全空間への射は、復元した射に一意に一致する。
方針：二つの射を B 上へ移し、随伴表示の自然性と基底変換同型で比較する。
規約：任意の試験対象 T についての一意性。
使われ方：制限の引き戻しの一意性。
-/
theorem partialSectionRestrictionLift_unique {Z A B T : SSet.{u}}
    (p : A ⟶ B) [Mono p] (q : Z ⟶ A) (s : T ⟶ A)
    (r : Over.mk (s ≫ p) ⟶ partialSectionObject p q) (t : T ⟶ Z)
    (htq : t ≫ q = s) (hti : t ≫ partialSectionInclusion p q = r.left) :
    t = partialSectionRestrictionLift p q s r := by
  let v : Over.mk (s ≫ p) ⟶ Over.mk (q ≫ p) := Over.homMk t (by
    change t ≫ (q ≫ p) = s ≫ p
    rw [← Category.assoc, htq])
  have hv : v ≫ partialSectionInclusionOver p q = r := Over.OverMorphism.ext hti
  have h := congrArg (partialSectionAdjunct p q) hv
  rw [partialSectionAdjunct_naturality, partialSectionAdjunct_inclusion] at h
  have hmap : (sliceFiberFunctor p).map v ≫ pullback.fst (q ≫ p) p =
      pullback.fst (s ≫ p) p ≫ t := sliceFiberFunctor_map_fst p v
  rw [hmap] at h
  apply (cancel_epi (monoBasePullbackIso p s).hom).mp
  change (monoBasePullbackIso p s).hom ≫ t = (monoBasePullbackIso p s).hom ≫
    ((monoBasePullbackIso p s).inv ≫ partialSectionAdjunct p q r)
  rw [Iso.hom_inv_id_assoc]
  exact h

end SerrePositivity.KST.Comparison
