module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.StrictInputCompactProjection
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.ExtendedInputComparison

/-!
概要：追加入力を保持した compact 成分対を元の引き戻しに厳密に貼る。
方針：共通入力への比較を第一脚で持ち上げ、制限した元の全余錐値を貼る。
規約：各成分の追加入力を保持し、元の pullback の全入力も保持する。
使われ方：compact comma の成分射影の下の試験余錐。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

variable {E D B K KE KD : SSet.{u + 1}}
  [Quasicategory E] [Quasicategory D] [Quasicategory B]
  (μ : Cardinal.{u}) (p : E ⟶ B) (q : D ⟶ B)
  (a : K ⟶ pullback p q) (z : JoinCocone a)

local notation "aE" => a ≫ pullback.fst p q
local notation "aD" => a ≫ pullback.snd p q
local notation "aB" => (a ≫ pullback.fst p q) ≫ p
local notation "zE" => mapJoinCocone (pullback.fst p q) z
local notation "zD" => mapJoinCocone (pullback.snd p q) z
local notation "zB" => mapJoinCocone p (mapJoinCocone (pullback.fst p q) z)

/-- 概要：追加入力付き像の比較同型から元の引き戻し内の compact な全頂点族を作る。
方針：第一脚の入力付き比較で同型を持ち上げ、制限後の全二成分を厳密に貼る。
規約：制限前の二つの追加入力付き頂点も同時に返す。
使われ方：指定成分始点を保持する全余錐への回収。 -/
lemma exists_extendedInputPullbackVertex_of_compatible_components
    (hp : F1B.EquivalenceLifting p)
    (aE' : KE ⟶ E) (aD' : KD ⟶ D)
    (iE : K ⟶ KE) [Mono iE] (iD : K ⟶ KD)
    (hiE : iE ≫ aE' = aE) (hiD : iD ≫ aD' = aD)
    (zE' : JoinCocone aE') (zD' : JoinCocone aD')
    (hziE : joinMap iE (𝟙 Δ[0]) ≫ zE'.val = (zE).val)
    (hziD : joinMap iD (𝟙 Δ[0]) ≫ zD'.val = (zD).val)
    (hQ : aD ≫ q = aB) (hZ : (zD).val ≫ q = (zB).val)
    (cE : (sliceOver ((SSet.yonedaEquiv (X := sliceUnder aE')).symm zE')) _⦋0⦌)
    (cD : (sliceOver ((SSet.yonedaEquiv (X := sliceUnder aD')).symm zD')) _⦋0⦌)
    (hcE : Compact.IsKappaCompact.{u, u + 1} μ
      ((sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder aE')).symm zE') ≫
        sliceUnderProjection aE').app (Opposite.op ⦋0⦌) cE))
    (hcD : Compact.IsKappaCompact.{u, u + 1} μ
      ((sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder aD')).symm zD') ≫
        sliceUnderProjection aD').app (Opposite.op ⦋0⦌) cD))
    (e : VertexIso
      ((relativeInputPostcomp aE' iE aE hiE zE' zE hziE p aB rfl zB rfl).app
        (Opposite.op ⦋0⦌) cE)
      ((relativeInputPostcomp aD' iD aD hiD zD' zD hziD q aB hQ zB hZ).app
        (Opposite.op ⦋0⦌) cD)) :
    ∃ (dE : (sliceOver ((SSet.yonedaEquiv (X := sliceUnder aE')).symm zE')) _⦋0⦌)
      (dD : (sliceOver ((SSet.yonedaEquiv (X := sliceUnder aD')).symm zD')) _⦋0⦌)
      (v : (sliceOver ((SSet.yonedaEquiv (X := sliceUnder a)).symm z)) _⦋0⦌),
      ComponentCompactVertex μ p q
        ((sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder a)).symm z) ≫
          sliceUnderProjection a).app (Opposite.op ⦋0⦌) v) ∧
      v.val ≫ sliceUnderPostcomp a (pullback.fst p q) =
        ((stableInputRestriction aE' iE aE hiE zE' zE hziE).app (Opposite.op ⦋0⦌) dE).val ∧
      v.val ≫ sliceUnderPostcomp a (pullback.snd p q) =
        ((stableInputRestriction aD' iD aD hiD zD' zD hziD).app (Opposite.op ⦋0⦌) dD).val := by
  let P := relativeInputPostcomp aE' iE aE hiE zE' zE hziE p aB rfl zB rfl
  let Q := relativeInputPostcomp aD' iD aD hiD zD' zD hziD q aB hQ zB hZ
  let RE := stableInputRestriction aE' iE aE hiE zE' zE hziE
  let RD := stableInputRestriction aD' iD aD hiD zD' zD hziD
  let d := pullbackVertexCandidate P Q
    (relativeInputPostcomp_equivalenceLifting aE' iE aE hiE zE' zE hziE p aB rfl zB rfl hp)
      cE cD e.symm
  let dE := (pullback.fst P Q).app (Opposite.op ⦋0⦌) d.vertex
  let dD := (pullback.snd P Q).app (Opposite.op ⦋0⦌) d.vertex
  let wE := RE.app (Opposite.op ⦋0⦌) dE
  let wD := RD.app (Opposite.op ⦋0⦌) dD
  have hd : (stableInputPostcomp aE p aB rfl zE zB rfl).app (Opposite.op ⦋0⦌) wE =
      (stableInputPostcomp aD q aB hQ zD zB hZ).app (Opposite.op ⦋0⦌) wD :=
    congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) d.vertex) (pullback.condition (f := P) (g := Q))
  obtain ⟨v, hf, hg⟩ := exists_inputPullbackSliceVertex_of_strict_components
    p q a z hQ hZ wE wD hd
  have hcE' : Compact.IsKappaCompact.{u, u + 1} μ
      ((sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder aE')).symm zE') ≫
        sliceUnderProjection aE').app (Opposite.op ⦋0⦌) dE) :=
    (Compact.isKappaCompact_iff_of_iso (VertexIso.map d.fstIso
      (sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder aE')).symm zE') ≫
        sliceUnderProjection aE'))).mpr hcE
  have hcD' : Compact.IsKappaCompact.{u, u + 1} μ
      ((sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder aD')).symm zD') ≫
        sliceUnderProjection aD').app (Opposite.op ⦋0⦌) dD) := by
    dsimp only [dD]
    rw [d.snd_eq]
    exact hcD
  have hwE : Compact.IsKappaCompact.{u, u + 1} μ
      ((sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder aE)).symm zE) ≫
        sliceUnderProjection aE).app (Opposite.op ⦋0⦌) wE) := by
    have htip := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) dE)
      (stableInputRestriction_base_projection aE' iE aE hiE zE' zE hziE)
    exact htip.symm ▸ hcE'
  have hwD : Compact.IsKappaCompact.{u, u + 1} μ
      ((sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder aD)).symm zD) ≫
        sliceUnderProjection aD).app (Opposite.op ⦋0⦌) wD) := by
    have htip := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) dD)
      (stableInputRestriction_base_projection aD' iD aD hiD zD' zD hziD)
    exact htip.symm ▸ hcD'
  exact ⟨dE, dD, v,
    inputVertex_componentCompact_of_val_eqs μ p q a z v wE wD hf hg hwE hwD, hf, hg⟩

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
