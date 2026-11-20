module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.BaseChangeMap
public import SerrePositivity.AlgebraicGeometry.BaseChangeChartCover

/-!
概要：KST §5 の blowup 比較射と標準チャート写像の両立。
方針：Proj の次数付き関手のアフィン局所公式を Rees 代数へ適用する。
規約：二つの実際のスキーム射の交換式として述べる。
使われ方：局所化した中心の blowup と基本開集合への制限の同型。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
variable {R S : Type u} [CommRing R] [CommRing S] (I : Ideal R) (f : R →+* S)

set_option backward.isDefEq.respectTransparency false in
/--
概要：blowup の係数比較射は各標準チャートで斉次局所化の比較射に等しい。
方針：次数一の中心元の像を同定し、Proj のアフィン局所公式を使う。
規約：KST §5、中心の像に対応する実際のチャートの包含射を用いる。
使われ方：局所化の場合の比較射の開埋め込み性と同型の証明。
-/
@[reassoc] theorem affineBlowupBaseMap_chart (a : I) :
    affineBlowupChartι (I.map f) (centerImageElement I _ f le_rfl a) ≫
      affineBlowupBaseMap I f =
      Spec.map (CommRingCat.ofHom (chartBaseChangeMap I _ f le_rfl a)) ≫
        affineBlowupChartι I a := by
  unfold affineBlowupChartι affineBlowupBaseMap chartBaseChangeMap
  exact proj_awayι_map_of_eq (reesGradedMap I (I.map f) f le_rfl)
    (reesGradedMap_irrelevant_le I f) 1 Nat.zero_lt_one (reesDegreeOne I a) (reesDegreeOne_mem I a)
    (reesDegreeOne _ (centerImageElement I _ f le_rfl a)) (reesDegreeOne_mem _ _)
    (reesMap_degreeOne I _ f le_rfl a) (reesDegreeOne_powers_le_comap I _ f le_rfl a)

/--
概要：blowup 比較射による標準チャートの逆像は、像の中心元の標準チャート。
方針：Proj の写像の基本開集合の逆像を計算する。
規約：KST §5、任意の係数環準同型に対する等式。
使われ方：チャート比較で構造射の制限全体を捉える。
-/
theorem affineBlowupBaseMap_preimage_chart (a : I) :
    affineBlowupBaseMap I f ⁻¹ᵁ affineBlowupChart I a =
      affineBlowupChart (I.map f) (centerImageElement I _ f le_rfl a) := by
  change Proj.basicOpen (reesGrade (I.map f))
    ((reesGradedMap I (I.map f) f le_rfl) (reesDegreeOne I a)) = _
  rw [show (reesGradedMap I (I.map f) f le_rfl) (reesDegreeOne I a) =
    reesDegreeOne (I.map f) (centerImageElement I _ f le_rfl a) from
      reesMap_degreeOne I _ f le_rfl a]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
概要：開部分スキームの比較図式で表せる射の制限は、チャートの射が開埋め込みなら開埋め込み。
方針：逆像の開集合を同定し、標的の開包含を消去してチャート同型で移送する。
規約：KST §5、逆像の全体に対応するチャートを仮定する。
使われ方：係数局所化による blowup 比較射の開埋め込み性。
-/
theorem isOpenImmersion_restrict_of_chart {X Y A B : Scheme.{u}} (g : X ⟶ Y)
    (U : X.Opens) (V : Y.Opens) (hU : g ⁻¹ᵁ V = U)
    (e : U.toScheme ≅ A) (t : V.toScheme ≅ B) (φ : A ⟶ B) [IsOpenImmersion φ]
    (h : e.inv ≫ U.ι ≫ g = φ ≫ t.inv ≫ V.ι) : IsOpenImmersion (g ∣_ V) := by
  subst U
  have heq : e.inv ≫ (g ∣_ V) = φ ≫ t.inv := by
    apply (cancel_mono V.ι).mp
    simpa only [Category.assoc, morphismRestrict_ι] using h
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsOpenImmersion e.inv, heq]
  infer_instance

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
