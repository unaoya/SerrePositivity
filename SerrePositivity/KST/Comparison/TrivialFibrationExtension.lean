module

public import SerrePositivity.KST.Comparison.PartialSectionRestrictionLift

/-!
# 単射に沿う trivial fibration の延長

概要：A→B が単射で Z→A が trivial fibration のとき、B 上へ厳密な引き戻しとして延長する。
方針：構成した部分切断の対象の普遍性を示し、その全体の持ち上げ性と合わせる。
規約：Segal 1974 Lemma 1.7 の厳密化への補助。延長の存在を追加仮定にはしない。
使われ方：二つのファイバーの共通模型を、span の端点の全空間へ延長する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits

/--
概要：単射上で部分切断の対象を制限すると、元の全空間に厳密な引き戻しとして戻る。
方針：随伴で戻した切断による復元の存在・基底条件・一意性を適用する。
規約：この引き戻し性は元の射の trivial fibration 性を要求しない。
使われ方：単射に沿う延長の制限の同定。
-/
theorem partialSectionInclusion_isPullback {Z A B : SSet.{u}}
    (p : A ⟶ B) [Mono p] (q : Z ⟶ A) :
    IsPullback (partialSectionInclusion p q) q (partialSectionObject p q).hom p := by
  apply IsPullback.mk' (partialSectionInclusion_base p q)
  · intro T φ φ' hi hq
    let s := φ ≫ q
    let r : Over.mk (s ≫ p) ⟶ partialSectionObject p q :=
      Over.homMk (φ ≫ partialSectionInclusion p q) (by
        change (φ ≫ partialSectionInclusion p q) ≫ (partialSectionObject p q).hom = (φ ≫ q) ≫ p
        rw [Category.assoc, partialSectionInclusion_base, ← Category.assoc])
    have hφ : φ = partialSectionRestrictionLift p q s r :=
      partialSectionRestrictionLift_unique p q s r φ rfl rfl
    have hφ' : φ' = partialSectionRestrictionLift p q s r :=
      partialSectionRestrictionLift_unique p q s r φ' hq.symm hi.symm
    exact hφ.trans hφ'.symm
  · intro T a b hab
    let r : Over.mk (b ≫ p) ⟶ partialSectionObject p q := Over.homMk a hab
    exact ⟨partialSectionRestrictionLift p q b r,
      partialSectionRestrictionLift_inclusion p q b r,
      partialSectionRestrictionLift_comp p q b r⟩

/--
概要：単射に沿う部分切断への包含は単射である。
方針：証明済みの引き戻しで単射性を移す。
規約：元の射の単射性や持ち上げ性は不要。
使われ方：延長の制限の部分対象としての扱い。
-/
instance partialSectionInclusion_mono {Z A B : SSet.{u}} (p : A ⟶ B) [Mono p] (q : Z ⟶ A) :
    Mono (partialSectionInclusion p q) :=
  (partialSectionInclusion_isPullback p q).mono_fst_of_mono

/--
概要：単射に沿って trivial fibration を延長し、元の全空間を厳密な引き戻しとして得る。
方針：部分切断の実対象、基底射、包含を取り、持ち上げ性と制限の普遍性を合わせる。
規約：trivial fibration は全ての単射に対する右持ち上げ性として指定する。
使われ方：一般の homotopy-cartesian な span の厳密化。
-/
theorem trivialFibrationExtension {Z A B : SSet.{u}} (p : A ⟶ B) [Mono p] (q : Z ⟶ A)
    (hq : (MorphismProperty.monomorphisms SSet.{u}).rlp q) :
    ∃ (E : SSet.{u}) (r : E ⟶ B) (i : Z ⟶ E),
      (MorphismProperty.monomorphisms SSet.{u}).rlp r ∧ IsPullback i q r p :=
  ⟨(partialSectionObject p q).left, (partialSectionObject p q).hom, partialSectionInclusion p q,
    partialSectionObject_allMono_rlp p q hq, partialSectionInclusion_isPullback p q⟩

end SerrePositivity.KST.Comparison
