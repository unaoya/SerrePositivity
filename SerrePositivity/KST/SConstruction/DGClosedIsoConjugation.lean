module
public import SerrePositivity.KST.SConstruction.DGFunctorClosedNaturality

/-! # 閉零同型による全 Hom 複体の共役
概要：対象ごとの閉零同型で dg 関手の値を移し、全 Hom の作用を保持する。
方針：豊穣前後合成と中間同型の相殺で単位・合成を検証する。
規約：H⁰ の同型を閉零同型として扱わない。使われ方：ラベル付き Perf の dg 作用。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded
section Enriched
variable (V : Type u) [Category V] [MonoidalCategory V]
  {C : Type v} [Category C] [EnrichedOrdinaryCategory V C]

/-- 同じ全次数 Hom 複体の前後を、実際の閉零同型で共役する。 -/
def enrichedClosedIsoConjugation {X X' Y Y' : C}
    (e : X ≅ X')
    (f : Y ≅ Y') :
    (X ⟶[V] Y) ⟶ (X' ⟶[V] Y') :=
  eHomWhiskerRight V e.inv Y ≫
    eHomWhiskerLeft V X' f.hom

/-- 共役は元の豊穣単位を移送先の単位へ送る。 -/
lemma enrichedClosedIsoConjugation_id {X X' : C}
    (e : X ≅ X') :
    eId V X ≫ enrichedClosedIsoConjugation V e e = eId V X' := by
  rw [← eHomEquiv_id, ← eHomEquiv_id]
  simp only [enrichedClosedIsoConjugation, ← Category.assoc, dgClosedHom_precompose,
    dgClosedHom_postcompose, Category.comp_id, Iso.inv_hom_id]

/-- 共役の中間同型は tensor 合成において厳密に相殺する。 -/
lemma enrichedClosedIsoConjugation_comp {X X' Y Y' Z Z' : C}
    (e : X ≅ X')
    (f : Y ≅ Y')
    (g : Z ≅ Z') :
    (enrichedClosedIsoConjugation V e f ⊗ₘ enrichedClosedIsoConjugation V f g) ≫
        eComp V X' Y' Z' =
      eComp V X Y Z ≫ enrichedClosedIsoConjugation V e g := by
  simp only [enrichedClosedIsoConjugation, tensorHom_def, comp_whiskerRight_assoc,
    MonoidalCategory.whiskerLeft_comp_assoc, Category.assoc]
  erw [← eComp_eHomWhiskerLeft]
  erw [eHom_whisker_cancel_assoc]
  erw [← eComp_eHomWhiskerRight_assoc]

/-- 共役は元の閉零同型そのものを全 Hom 自然な比較として保持する。 -/
lemma enrichedClosedIsoConjugation_naturality {X X' Y Y' : C}
    (e : X ≅ X') (f : Y ≅ Y') :
    enrichedClosedIsoConjugation V e f ≫ eHomWhiskerRight V e.hom Y' =
      eHomWhiskerLeft V X f.hom := by
  rw [enrichedClosedIsoConjugation, Category.assoc, eHom_whisker_exchange,
    ← Category.assoc, ← eHomWhiskerRight_comp, Iso.hom_inv_id,
    eHomWhiskerRight_id, Category.id_comp]

variable {D : Type w} [EnrichedCategory V D] (F : EnrichedFunctor V D C)
  (b : D → C) (e : ∀ x, F.obj x ≅ b x)

/-- 豊穣関手の対象を、対象別の実同型を使って移す。 -/
def enrichedFunctorClosedConjugate : EnrichedFunctor V D C where
  obj := b
  map x y := F.map x y ≫ enrichedClosedIsoConjugation V (e x) (e y)
  map_id x := by
    rw [← Category.assoc, F.map_id, enrichedClosedIsoConjugation_id]
  map_comp x y z := by
    rw [← tensorHom_comp_tensorHom_assoc, enrichedClosedIsoConjugation_comp,
      ← Category.assoc, F.map_comp, Category.assoc]

end Enriched

variable (A : Type u) [CommRing A] {C : Type v} [DGCategory A C]
variable {D : Type w} [DGCategory A D] (F : DGFunctor A D C)

/-- 全 Hom を保ったまま、標的を同じ dg 圏の閉零対象表示にする。 -/
def dgFunctorClosedTarget : EnrichedFunctor (Complex A) D (ClosedCategory A C) where
  obj x := ForgetEnrichment.of (Complex A) (F.obj x)
  map := F.map
  map_id := F.map_id
  map_comp := F.map_comp

variable (b : D → C)
  (e : ∀ x, ForgetEnrichment.of (Complex A) (F.obj x) ≅
    ForgetEnrichment.of (Complex A) (b x))

/-- 元の対象別閉零同型で値を共役した dg 関手。 -/
def dgFunctorClosedConjugate : DGFunctor A D C where
  obj := b
  map := (enrichedFunctorClosedConjugate (Complex A) (dgFunctorClosedTarget A F)
    (fun x => ForgetEnrichment.of (Complex A) (b x)) e).map
  map_id := (enrichedFunctorClosedConjugate (Complex A) (dgFunctorClosedTarget A F)
    (fun x => ForgetEnrichment.of (Complex A) (b x)) e).map_id
  map_comp := (enrichedFunctorClosedConjugate (Complex A) (dgFunctorClosedTarget A F)
    (fun x => ForgetEnrichment.of (Complex A) (b x)) e).map_comp

/-- 元の閉零同型は、共役した dg 関手への全 Hom 自然比較になる。 -/
lemma dgFunctorClosedConjugate_naturality (x y : D) :
    F.map x y ≫ eHomWhiskerLeft (Complex A)
        (ForgetEnrichment.of (Complex A) (F.obj x)) (e y).hom =
      (dgFunctorClosedConjugate A F b e).map x y ≫
        eHomWhiskerRight (Complex A) (e x).hom
          (ForgetEnrichment.of (Complex A) (b y)) := by
  change F.map x y ≫ _ = (F.map x y ≫
    enrichedClosedIsoConjugation (Complex A) (e x) (e y)) ≫ _
  rw [Category.assoc]
  exact congrArg (fun k => F.map x y ≫ k)
    (enrichedClosedIsoConjugation_naturality (Complex A) (e x) (e y)).symm

end SerrePositivity.KST.SConstruction
