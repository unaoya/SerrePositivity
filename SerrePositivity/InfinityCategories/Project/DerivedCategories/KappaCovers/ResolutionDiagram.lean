module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.PartialMaps
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.PartialSemifree
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.ResolutionCovering
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.PresentationReduction

/-!
概要：標準 semifree resolution の κ-filtered strict 余極限表示。
方針：依存閉セル選択を関手にし、次数ごとの単射性と全要素の網羅性で余極限性を得る。
規約：表示の存在を入力に置かず、全て実 dg 加群のデータから作る。
使われ方：D-8 d の native/strict 比較へ渡す表示。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (M : ModuleCategory R D) (κ : Cardinal.{u}) [Fact κ.IsRegular]

def dgKappaResolutionPiecesDiagram : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.DGKappaResolutionPieces R D M κ ⥤ ModuleCategory R D where
  obj s := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaPartialResolution R D M s.val s.property.2
  map {s t} h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaPartialResolutionMap R D M s.val t.val s.property.2 t.property.2 (leOfHom h)
  map_id s := by
    letI := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaPartialResolutionInclusion_mono R D M s.val s.property.2
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaPartialResolutionInclusion R D M s.val s.property.2)).1
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaPartialResolutionMap_inclusion, Category.id_comp]
  map_comp {s t r} h k := by
    letI := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaPartialResolutionInclusion_mono R D M r.val r.property.2
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaPartialResolutionInclusion R D M r.val r.property.2)).1
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaPartialResolutionMap_inclusion, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaPartialResolutionMap_inclusion, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaPartialResolutionMap_inclusion]

def dgKappaResolutionPiecesCocone : Cocone (dgKappaResolutionPiecesDiagram R D M κ) where
  pt := moduleResolutionCandidate R D M
  ι :=
    { app s := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaPartialResolutionInclusion R D M s.val s.property.2
      naturality s t h := by
        change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaPartialResolutionMap R D M s.val t.val s.property.2 t.property.2
          (leOfHom h) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaPartialResolutionInclusion R D M t.val t.property.2 =
            _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaPartialResolutionInclusion R D M s.val s.property.2 ≫ 𝟙 _
        exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaPartialResolutionMap_inclusion R D M _ _ _ _ _).trans
          (Category.comp_id _).symm }

def dgKappaResolutionPiecesIsColimit (hκ : Cardinal.aleph0 < κ) :
    IsColimit (dgKappaResolutionPiecesCocone R D M κ) := by
  letI := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionPieces_isCardinalFiltered R D M κ
  letI := isFiltered_of_isCardinalFiltered (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.DGKappaResolutionPieces R D M κ) κ
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaModuleFilteredUnionIsColimit R D (dgKappaResolutionPiecesDiagram R D M κ)
    (dgKappaResolutionPiecesCocone R D M κ)
    (fun s => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaPartialResolutionInclusion_degreewiseMono R D M s.val s.property.2)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaPartialResolution_jointlySurjective R D M hκ)

def dgKappaResolutionStrictRepresentativePresentation (hκ : Cardinal.aleph0 < κ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.DGKappaStrictRepresentativePresentation R D κ (moduleResolutionCandidate R D M) where
  Index := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.DGKappaResolutionPieces R D M κ
  order := inferInstance
  filtered := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionPieces_isCardinalFiltered R D M κ
  diagram := dgKappaResolutionPiecesDiagram R D M κ
  cocone := dgKappaResolutionPiecesCocone R D M κ
  isColimit := dgKappaResolutionPiecesIsColimit R D M κ hκ
  iso := Iso.refl _
  stageCovers s := by
    obtain ⟨N, hN, ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaPartialResolution_representativeCovers R D M s.val s.property.2
      hκ (Fact.out : κ.IsRegular) s.property.1
    exact ⟨N, hN, ⟨((moduleToHomotopyDerivedIso R D).app N).symm ≪≫
      (moduleHomotopyToDerivedClosed R D).mapIso e ≪≫
        (moduleToHomotopyDerivedIso R D).app _⟩⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
