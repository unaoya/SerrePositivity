module

public import SerrePositivity.BhattScholze.Prismatic.Site.FlatCechConerve
public import SerrePositivity.BhattScholze.Prismatic.Site.FlatPushoutResidue
public import SerrePositivity.BhattScholze.Prismatic.Site.FlatSiteSheaf
import all Mathlib.AlgebraicTopology.CechNerve

/-!
# 完備 Čech 余脈体の有限剰余の比較

## 概要
site の Čech 余脈体を基底対象の下で読み、各次数の剰余押し出しから余脈体の比較を作る。

## 方針
基底脚と各挿入を固定する余極限の一意性を、すべての単体射に適用する。

## 規約
BS 著者版 Corollary 3.12 (c)。有限剰余の押し出し性を仮定する比較部分。

## 使われ方
有限剰余での増大 Čech 完全性を、完備 Čech 複体に移す。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
-- 余脈体の型と基底の下の圏を照合するため。
set_option maxHeartbeats 750000

universe u

namespace SerrePositivity.BhattScholze.Prismatic.PrismOver

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {P : OrientedPrism p A}
variable {R : Type u} [CommRing R] [Algebra (A ⧸ P.ideal) R] {κ : Cardinal.{u}}
variable {X Y : PrismOver P R κ}

/-- 概要：基底対象から延長したイデアルで台の環を剰余する関手。
方針：基底の下の圏で各対象への延長イデアルと誘導商射を取る。
規約：イデアルは固定し、基底からの射を各対象に保持する。
使われ方：BS 著者版 Corollary 3.12 の有限剰余と遷移写像。 -/
@[expose] def flatResidueRing (J : Ideal X.B) : Under X ⥤ CommRingCat.{u} where
  obj Z := CommRingCat.of (Z.right.B ⧸ J.map Z.hom.toHom.toRingHom)
  map {U V} k := CommRingCat.ofHom (Ideal.quotientMap (J.map V.hom.toHom.toRingHom)
    k.right.toHom.toRingHom (by
      apply Ideal.map_le_iff_le_comap.mp
      rw [Ideal.map_map]
      have w := congrArg (fun f : X ⟶ V.right ↦ f.toHom.toRingHom) (Under.w k)
      change k.right.toHom.toRingHom.comp U.hom.toHom.toRingHom =
        V.hom.toHom.toRingHom at w
      rw [w]))
  map_id := by
    intro U
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext x
    rfl
  map_comp := by
    intro U V W k l
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext x
    rfl

/-- 包含するイデアルから小さい剰余へ移る、余脈体の各脚と可換な自然変換。 -/
@[expose] def flatResidueTransition {J K : Ideal X.B} (h : J ≤ K) :
    flatResidueRing J ⟶ flatResidueRing K where
  app Z := CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.map_mono h))
  naturality := by
    intro U V k
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext x
    rfl

variable (hκ : IsAdmissibleCutoff P R κ) (f : X ⟶ Y) (hf : IsFaithfullyFlat f)

/-- 各次数に基底からの脚を保持した増大 Čech 余脈体。 -/
@[expose] def flatCechUnder : CosimplicialObject.Augmented (Under X) where
  left := Under.mk (𝟙 X)
  right :=
    { obj := fun n ↦ Under.mk ((flatAugmentedCechConerve hκ f hf).hom.app n)
      map := fun φ ↦ Under.homMk ((flatAugmentedCechConerve hκ f hf).right.map φ) (by
        have h := (flatAugmentedCechConerve hκ f hf).hom.naturality φ
        exact h.symm.trans (Category.id_comp _))
      map_id := by
        intro n
        ext : 1
        exact (flatAugmentedCechConerve hκ f hf).right.map_id n
      map_comp := by
        intro i j k φ ψ
        ext : 1
        exact (flatAugmentedCechConerve hκ f hf).right.map_comp φ ψ }
  hom :=
    { app := fun n ↦ Under.homMk ((flatAugmentedCechConerve hκ f hf).hom.app n) (by simp)
      naturality := fun _ _ _ ↦ (Under.mkIdInitial (X := X)).hom_ext _ _ }

/-- 広い押し出しの各脚を、基底の下の圏の射として取る。 -/
@[expose] def flatCechInclusion (n : SimplexCategory) (i : Fin (n.len + 1)) :
    Under.mk f ⟶ (flatCechUnder hκ f hf).right.obj n := by
  letI := hasWidePushout_flat hκ f hf (n.len + 1)
  exact Under.homMk (WidePushout.ι (fun _ : Fin (n.len + 1) ↦ f) i)
    (WidePushout.arrow_ι (fun _ : Fin (n.len + 1) ↦ f) i)

@[reassoc]
theorem flatCechInclusion_naturality {m n : SimplexCategory} (φ : m ⟶ n)
    (i : Fin (m.len + 1)) :
    flatCechInclusion hκ f hf m i ≫ (flatCechUnder hκ f hf).right.map φ =
      flatCechInclusion hκ f hf n (φ.toOrderHom i) := by
  letI := hasWidePushout_flat hκ f hf (m.len + 1)
  letI := hasWidePushout_flat hκ f hf (n.len + 1)
  ext : 1
  exact WidePushout.ι_desc (fun _ : Fin (m.len + 1) ↦ f) _ _ _ i

/-- site の完備 Čech 余脈体の各項を同じ基底イデアルで剰余する。 -/
@[expose] def flatResidueCech (J : Ideal X.B) : CosimplicialObject.Augmented CommRingCat.{u} :=
  (CosimplicialObject.Augmented.whiskeringObj _ _ (flatResidueRing J)).obj
    (flatCechUnder hκ f hf)

/-- 基底の下の圏で、剰余 Čech 余脈体の増大射を取る。 -/
@[expose] def flatResidueArrow (J : Ideal X.B) : Arrow CommRingCat.{u} :=
  Arrow.mk ((flatResidueRing J).map ((Under.mkIdInitial (X := X)).to (Under.mk f)))

/-- 有限剰余を取った Čech 項への挿入。 -/
abbrev flatResidueCechLeg (J : Ideal X.B) (n : SimplexCategory) (i : Fin (n.len + 1)) :=
  (flatResidueRing J).map (flatCechInclusion hκ f hf n i)

/-- 完備 Čech の有限剰余を、通常の広い span の cocone として読む。 -/
@[expose] def flatResidueCocone (J : Ideal X.B) (n : SimplexCategory) :
    Cocone (repeatedWideSpan (flatResidueArrow f J).hom (n.len + 1)) :=
  WidePushoutShape.mkCocone ((flatResidueCech hκ f hf J).hom.app n)
    (flatResidueCechLeg hκ f hf J n) (by
      intro i
      change (flatResidueRing J).map _ ≫ (flatResidueRing J).map _ =
        (flatResidueRing J).map _
      rw [← Functor.map_comp]
      congr 1
      exact (Under.mkIdInitial (X := X)).hom_ext _ _)

variable (J : Ideal X.B)
variable (hJ : ∀ n, IsColimit (flatResidueCocone hκ f hf J n))

private def residueObjIso (n : SimplexCategory) :
    (flatResidueCech hκ f hf J).right.obj n ≅ (flatResidueArrow f J).cechConerve.obj n :=
  (hJ n).coconePointUniqueUpToIso (colimit.isColimit _)

private theorem residueObjIso_fac (n : SimplexCategory) (i : Fin (n.len + 1)) :
    flatResidueCechLeg hκ f hf J n i ≫ (residueObjIso hκ f hf J hJ n).hom =
      WidePushout.ι (fun _ : Fin (n.len + 1) ↦ (flatResidueArrow f J).hom) i :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (hJ n) (colimit.isColimit _) (some i)

private theorem residueObjIso_head (n : SimplexCategory) :
    (flatResidueCech hκ f hf J).hom.app n ≫ (residueObjIso hκ f hf J hJ n).hom =
      WidePushout.head (fun _ : Fin (n.len + 1) ↦ (flatResidueArrow f J).hom) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (hJ n) (colimit.isColimit _) none

/-- 概要：有限剰余が各次数で押し出しなら、増大 Čech 余脈体の比較は同型。
方針：余極限の一意性で余面・余退化・増大を同時に追跡する。
規約：BS 著者版 Corollary 3.12 (c)。比較は環側で行う。
使われ方：通常の忠実平坦降下を完備 Čech 余脈体の剰余へ移す。 -/
def flatResidueCechIso :
    flatResidueCech hκ f hf J ≅ (flatResidueArrow f J).augmentedCechConerve := by
  let e := residueObjIso hκ f hf J hJ
  refine Comma.isoMk (Iso.refl _) (NatIso.ofComponents e ?_) ?_
  · intro m n φ
    apply (hJ m).hom_ext
    rintro (_ | i)
    · let S := flatResidueCech hκ f hf J
      have hε : S.hom.app m ≫ S.right.map φ = S.hom.app n := by
        have h := (S.hom.naturality φ).symm
        change S.hom.app m ≫ S.right.map φ = 𝟙 _ ≫ S.hom.app n at h
        simpa only [Category.id_comp] using h
      change S.hom.app m ≫ S.right.map φ ≫ (e n).hom =
        S.hom.app m ≫ (e m).hom ≫ _
      rw [← Category.assoc, hε, residueObjIso_head, ← Category.assoc, residueObjIso_head]
      exact (WidePushout.head_desc _ _ _ _).symm
    · let S := flatResidueCech hκ f hf J
      have hl : flatResidueCechLeg hκ f hf J m i ≫ S.right.map φ =
          flatResidueCechLeg hκ f hf J n (φ.toOrderHom i) := by
        change (flatResidueRing J).map (flatCechInclusion hκ f hf m i) ≫
          (flatResidueRing J).map ((flatCechUnder hκ f hf).right.map φ) = _
        rw [← Functor.map_comp, flatCechInclusion_naturality]
      change flatResidueCechLeg hκ f hf J m i ≫ S.right.map φ ≫ (e n).hom =
        flatResidueCechLeg hκ f hf J m i ≫ (e m).hom ≫ _
      rw [← Category.assoc, hl, residueObjIso_fac, ← Category.assoc, residueObjIso_fac]
      let a := flatResidueArrow f J
      let s (j : Fin (m.len + 1)) :=
        WidePushout.ι (fun _ : Fin (n.len + 1) ↦ a.hom) (φ.toOrderHom j)
      let b := WidePushout.head (fun _ : Fin (n.len + 1) ↦ a.hom)
      exact (WidePushout.ι_desc (fun _ : Fin (m.len + 1) ↦ a.hom) b s
        (fun j ↦ WidePushout.arrow_ι (fun _ : Fin (n.len + 1) ↦ a.hom) (φ.toOrderHom j)) i).symm
  · apply NatTrans.ext
    funext n
    simpa using (residueObjIso_head hκ f hf J hJ n).symm

/-- 剰余の遷移を増大 Čech 余脈体の各次数に適用する。 -/
@[expose] def flatResidueCechTransition {J K : Ideal X.B} (h : J ≤ K) :
    flatResidueCech hκ f hf J ⟶ flatResidueCech hκ f hf K :=
  ((CosimplicialObject.Augmented.whiskering _ _).map (flatResidueTransition h)).app
    (flatCechUnder hκ f hf)

/-- 剰余の遷移が被覆の剰余射の間に誘導する可換正方形。 -/
def flatResidueArrowTransition {J K : Ideal X.B} (h : J ≤ K) :
    flatResidueArrow f J ⟶ flatResidueArrow f K :=
  Arrow.homMk ((flatResidueTransition h).app (Under.mk (𝟙 X)))
    ((flatResidueTransition h).app (Under.mk f))
    ((flatResidueTransition h).naturality ((Under.mkIdInitial (X := X)).to (Under.mk f))).symm

/-- 概要：増大 Čech 余脈体の剰余同型はイデアルの包含と可換。
方針：基底脚と各挿入を調べ、広い押し出しの一意性を使う。
規約：BS 著者版 Corollary 3.12 (c) の有限剰余の遷移。
使われ方：次数ごとの逆極限上で比較同型を取る。 -/
theorem flatResidueCechIso_naturality {K : Ideal X.B} (h : K ≤ J)
    (hK : ∀ n, IsColimit (flatResidueCocone hκ f hf K n)) :
    flatResidueCechTransition hκ f hf h ≫ (flatResidueCechIso hκ f hf J hJ).hom =
      (flatResidueCechIso hκ f hf K hK).hom ≫
        Arrow.mapAugmentedCechConerve (flatResidueArrowTransition f h) := by
  apply Comma.hom_ext
  · change (flatResidueTransition h).app (Under.mk (𝟙 X)) ≫ 𝟙 _ =
        𝟙 _ ≫ (flatResidueTransition h).app (Under.mk (𝟙 X))
    simp
  · apply NatTrans.ext
    funext n
    apply (hK n).hom_ext
    rintro (_ | i)
    · let a := (flatCechUnder hκ f hf).hom.app n
      let t := flatResidueTransition h
      change (flatResidueRing K).map a ≫ (t.app _) ≫ (residueObjIso hκ f hf J hJ n).hom =
        (flatResidueRing K).map a ≫ (residueObjIso hκ f hf K hK n).hom ≫ _
      have hmJ := residueObjIso_head hκ f hf J hJ n
      have hmK := residueObjIso_head hκ f hf K hK n
      change (flatResidueRing J).map a ≫ _ = _ at hmJ
      change (flatResidueRing K).map a ≫ _ = _ at hmK
      rw [← Category.assoc, t.naturality, Category.assoc, hmJ,
        ← Category.assoc, hmK]
      exact (WidePushout.head_desc _ _ _ _).symm
    · let a := flatCechInclusion hκ f hf n i
      let t := flatResidueTransition h
      change (flatResidueRing K).map a ≫ (t.app _) ≫ (residueObjIso hκ f hf J hJ n).hom =
        (flatResidueRing K).map a ≫ (residueObjIso hκ f hf K hK n).hom ≫ _
      rw [← Category.assoc, t.naturality, Category.assoc, residueObjIso_fac,
        ← Category.assoc, residueObjIso_fac]
      let a := flatResidueArrowTransition f h
      let s (j : Fin (n.len + 1)) :=
        a.right ≫ WidePushout.ι (fun _ : Fin (n.len + 1) ↦ (flatResidueArrow f J).hom) j
      let b := a.left ≫ WidePushout.head (fun _ : Fin (n.len + 1) ↦ (flatResidueArrow f J).hom)
      exact (WidePushout.ι_desc (fun _ : Fin (n.len + 1) ↦ (flatResidueArrow f K).hom) b s
        (fun j ↦ by
          change (flatResidueArrow f K).hom ≫
            a.right ≫ WidePushout.ι (fun _ : Fin (n.len + 1) ↦ (flatResidueArrow f J).hom) j = b
          rw [← Arrow.w_assoc a]
          exact congrArg (fun z ↦ a.left ≫ z)
            (WidePushout.arrow_ι (fun _ : Fin (n.len + 1) ↦ (flatResidueArrow f J).hom) j)) i).symm

end SerrePositivity.BhattScholze.Prismatic.PrismOver
