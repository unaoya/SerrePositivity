module
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementShiftEvaluation
public import SerrePositivity.DifferentialGraded.Category.TriangleComparison

/-! # 実際のperfect dg cone三角形と主導来三角構造の一致 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 実際のconnecting射の主導来比較は、整合的shiftと標準比較同型で可換となる。 -/
lemma perfectDGModuleConeConnecting_toDerived (S : Set D) (M N : PerfectDGModuleOver A D S)
    (f : ForgetEnrichment.of (Complex A) M.val ⟶ ForgetEnrichment.of (Complex A) N.val) :
    ((perfectDGModuleToDerived A D S).map
      (perfectDGModuleHomotopyMap A D S
        (M := perfectDGModuleCone A D S M N f) (N := perfectDGModuleShiftObj A D S 1 M)
        (moduleConeConnecting A D f)) ≫
      ((perfectDGModuleToDerived A D S).commShiftIso (1 : ℤ)).hom.app
        (perfectDGModuleHomotopyObj A D S M)) ≫
      ((moduleToHomotopyDerivedIso A D).hom.app
        (ForgetEnrichment.of (Complex A) M.val))⟦(1 : ℤ)⟧' =
    (moduleToHomotopyDerivedIso A D).hom.app (moduleCone A D f) ≫
      (moduleToDerived A D).map (moduleConeConnecting A D f) ≫
      ((moduleToDerived A D).commShiftIso (1 : ℤ)).hom.app
        (ForgetEnrichment.of (Complex A) M.val) := by
  let X : ModuleCategory A D := ForgetEnrichment.of (Complex A) M.val
  let F := perfectDGModuleToDerived A D S
  let g := perfectDGModuleHomotopyMap A D S
    (M := perfectDGModuleCone A D S M N f) (N := perfectDGModuleShiftObj A D S 1 M)
    (moduleConeConnecting A D f)
  let e := moduleToHomotopyDerivedIso A D
  have hs := (perfectDGModuleToDerived_commShiftIso_hom_app A D S (1 : ℤ)
    (perfectDGModuleHomotopyObj A D S M)).trans
      (perfectDGModuleShiftHomotopyDerivedIso_hom_obj A D S (1 : ℤ) M)
  have hn := NatTrans.shift_app_comm e.hom (1 : ℤ) X
  have hm := perfectDGModuleHomotopyMap_toDerived A D S
    (M := perfectDGModuleCone A D S M N f) (N := perfectDGModuleShiftObj A D S 1 M)
    (moduleConeConnecting A D f)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => F.map g ≫ a)
      ((congrArg (fun a => a ≫ (e.hom.app X)⟦(1 : ℤ)⟧') hs).trans hn)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun a => a ≫ ((moduleToDerived A D).commShiftIso (1 : ℤ)).hom.app X) hm).trans
          (Category.assoc _ _ _))))

/-- 主導来関手で写した標準三角形の第三射を、実際のconnecting射で計算する。 -/
lemma perfectDGModuleConeTriangle_toDerived_mor₃ (S : Set D) (M N : PerfectDGModuleOver A D S)
    (f : ForgetEnrichment.of (Complex A) M.val ⟶ ForgetEnrichment.of (Complex A) N.val) :
    ((perfectDGModuleToDerived A D S).mapTriangle.obj
      (perfectDGModuleConeTriangle A D S M N f)).mor₃ =
    (perfectDGModuleToDerived A D S).map
      (perfectDGModuleHomotopyMap A D S
        (M := perfectDGModuleCone A D S M N f) (N := perfectDGModuleShiftObj A D S 1 M)
        (moduleConeConnecting A D f)) ≫
      ((perfectDGModuleToDerived A D S).commShiftIso (1 : ℤ)).hom.app
        (perfectDGModuleHomotopyObj A D S M) :=
  perfectDGModuleConeTriangle_map_mor₃ A D S (perfectDGModuleToDerived A D S) M N f


/-- 実際のdg cone三角形の主導来像は、元の加群の主導来cone三角形と同型である。 -/
def perfectDGModuleConeTriangleToDerivedIso (S : Set D) (M N : PerfectDGModuleOver A D S)
    (f : ForgetEnrichment.of (Complex A) M.val ⟶ ForgetEnrichment.of (Complex A) N.val) :
    (perfectDGModuleToDerived A D S).mapTriangle.obj (perfectDGModuleConeTriangle A D S M N f) ≅
      moduleDerivedConeTriangle A D f := by
  let e := moduleToHomotopyDerivedIso A D
  refine Triangle.isoMk _ _ (e.app (ForgetEnrichment.of (Complex A) M.val))
    (e.app (ForgetEnrichment.of (Complex A) N.val)) (e.app (moduleCone A D f)) ?_ ?_ ?_
  · exact perfectDGModuleHomotopyMap_toDerived A D S f
  · exact perfectDGModuleHomotopyMap_toDerived A D S
      (M := N) (N := perfectDGModuleCone A D S M N f) (moduleConeInr A D f)
  · exact (congrArg (fun a => a ≫ (e.hom.app (ForgetEnrichment.of (Complex A) M.val))⟦(1 : ℤ)⟧')
      (perfectDGModuleConeTriangle_toDerived_mor₃ A D S M N f)).trans
        (perfectDGModuleConeConnecting_toDerived A D S M N f)

/-- 実際の標準dg cone三角形は、構成したH⁰三角構造でdistinguishedである。 -/
lemma perfectDGModuleConeTriangle_distinguished (S : Set D) (M N : PerfectDGModuleOver A D S)
    (f : ForgetEnrichment.of (Complex A) M.val ⟶ ForgetEnrichment.of (Complex A) N.val) :
    perfectDGModuleConeTriangle A D S M N f ∈ distTriang (PerfectDGHomotopyCategoryOver A D S) := by
  apply ((perfectDGModuleToDerived A D S).map_distinguished_iff _).mp
  exact isomorphic_distinguished _ (moduleDerivedConeTriangle_distinguished A D f) _
    (perfectDGModuleConeTriangleToDerivedIso A D S M N f)

/-- 閉零部分圏の射からのH⁰像を、全加群への包含を経由した像から復元する。 -/
lemma perfectDGModuleHomotopyMap_onClosed (S : Set D)
    {X Y : ClosedCategory A (PerfectDGModuleOver A D S)} (f : X ⟶ Y) :
    perfectDGModuleHomotopyMap A D S
      (M := ForgetEnrichment.to (Complex A) X) (N := ForgetEnrichment.to (Complex A) Y)
      ((perfectDGModuleInclusion A D S).onClosed.map f) =
    (toHomotopy A (PerfectDGModuleOver A D S)).map f :=
  congrArg (fun g => (toHomotopy A (PerfectDGModuleOver A D S)).map g)
    ((perfectDGModuleInclusion A D S).onClosed.preimage_map f)

/-- H⁰のdistinguished三角形は、実際の射影的perfect dg加群の標準cone三角形の同型閉包である。 -/
lemma perfectDGHomotopy_distinguished_iff_cone (S : Set D)
    (T : Triangle (PerfectDGHomotopyCategoryOver A D S)) :
    T ∈ distTriang (PerfectDGHomotopyCategoryOver A D S) ↔
      ∃ (M N : PerfectDGModuleOver A D S)
        (f : ForgetEnrichment.of (Complex A) M.val ⟶ ForgetEnrichment.of (Complex A) N.val),
        Nonempty (T ≅ perfectDGModuleConeTriangle A D S M N f) := by
  constructor
  · intro hT
    let M : PerfectDGModuleOver A D S := ForgetEnrichment.to (Complex A) T.obj₁.as
    let N : PerfectDGModuleOver A D S := ForgetEnrichment.to (Complex A) T.obj₂.as
    obtain ⟨f, hf⟩ := (toHomotopy A (PerfectDGModuleOver A D S)).map_surjective T.mor₁
    let g : ForgetEnrichment.of (Complex A) M.val ⟶ ForgetEnrichment.of (Complex A) N.val :=
      (perfectDGModuleInclusion A D S).onClosed.map f
    have hg : (perfectDGModuleConeTriangle A D S M N g).mor₁ = T.mor₁ :=
      (perfectDGModuleHomotopyMap_onClosed A D S f).trans hf
    have he : Arrow.mk (perfectDGModuleConeTriangle A D S M N g).mor₁ ≅ Arrow.mk T.mor₁ :=
      Arrow.isoMk' _ _ (Iso.refl T.obj₁) (Iso.refl T.obj₂)
        ((Category.id_comp _).trans (hg.symm.trans (Category.comp_id _).symm))
    obtain ⟨e, _⟩ := exists_iso_of_arrow_iso (perfectDGModuleConeTriangle A D S M N g) T
      (perfectDGModuleConeTriangle_distinguished A D S M N g) hT he
    exact ⟨M, N, g, ⟨e.symm⟩⟩
  · rintro ⟨M, N, f, ⟨e⟩⟩
    exact isomorphic_distinguished _ (perfectDGModuleConeTriangle_distinguished A D S M N f) _ e

end SerrePositivity.DifferentialGraded
