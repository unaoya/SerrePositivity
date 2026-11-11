module

public import SerrePositivity.KST.Spectra.FilteredFiniteMappingColimit
public import SerrePositivity.KST.Spectra.SuspensionLoop
public import SerrePositivity.Spectra.PointedSimplicialSet.AdjoinBasepointUnit
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-!
概要：点つき loop 対象と filtered colimit の標準比較同型。
方針：単体的円の有限性と有限な点つき源からの内部 Hom の余極限保存を使う。
規約：スペクトルの ∞ 余極限の主張ではなく、各段の通常の点つき単体集合の同型。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。telescope の Ω 条件。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：標準単体の境界を潰した点つき球面の基礎単体集合は有限。
方針：有限な境界・標準単体・点の押し出しとして示す。
規約：零次球面を含む全自然数 n。
使われ方：Goerss–Jardine I §7、BF 1978 §2。loop の源である円の有限性。 -/
instance pointedSphere_finite (n : ℕ) : (PointedSimplicialSet.sphere.{u} n).right.Finite := by
  let : (𝟙_ SSet.{u}).Finite := finite_of_iso PointedSimplicialSet.deltaZeroUnitIso.{u}
  change (pushout (boundary.{u} n).ι (toUnit (boundary.{u} n : SSet.{u}))).Finite
  apply finite_of_isColimit
    (pushoutIsPushout (boundary.{u} n).ι (toUnit (boundary.{u} n : SSet.{u})))
  rintro (_ | _ | _) <;> dsimp <;> infer_instance

variable {J : Type u} [SmallCategory J] [IsFiltered J] (D : J ⥤ PointedSimplicialSet.{u})

/-- 概要：点つき loop 関手は filtered colimit を保存する。
方針：有限な円からの点つき内部 Hom の余極限保存を使う。
規約：Kan 性は要求しない。
使われ方：Goerss–Jardine I §7、HA §1.4.2。段ごとの Ω 条件と filtered colimit の整合性。 -/
instance loop_preservesFilteredDiagram :
    PreservesColimit D (ihom PointedSimplicialSet.circle.{u}) := by
  change PreservesColimit D (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u})
  infer_instance

/-- 概要：loop 対象の filtered colimit と余極限の loop 対象との標準同型。
方針：loop 関手の余極限保存の比較同型を逆向きに使う。
規約：通常の点つき単体集合の同型。
使われ方：BF 1978 §2、HA §1.4.2。filtered Ω 列の構造射の比較。 -/
def loopFilteredColimitIso :
    colimit (D ⋙ ihom PointedSimplicialSet.circle.{u}) ≅ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (colimit D) :=
  (preservesColimitIso (ihom PointedSimplicialSet.circle.{u}) D).symm

/-- 概要：loop と余極限の比較同型を各段へ制限すると cocone 射の loop。
方針：余極限保存の標準比較の成分を計算する。
規約：点つき射の厳密な等式。
使われ方：BF 1978 §2、HA §1.4.2。Ω 条件と π_* の比較の可換式。 -/
@[reassoc (attr := simp)]
theorem loopFilteredColimitIso_ι (j : J) :
    colimit.ι (D ⋙ ihom PointedSimplicialSet.circle.{u}) j ≫ (loopFilteredColimitIso D).hom =
      PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (colimit.ι D j) :=
  ι_preservesColimitIso_inv (ihom PointedSimplicialSet.circle.{u}) D j

end

end SerrePositivity.KST.Spectra
