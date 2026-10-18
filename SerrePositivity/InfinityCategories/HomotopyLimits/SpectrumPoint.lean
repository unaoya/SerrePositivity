module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpectrumBinaryProduct

/-!
概要：各段が一点の Ω スペクトル。
方針：懸垂と loop の随伴と一点の零対象性から構造射とその随伴の同型性を得る。
規約：L9 の単射構造射と全基点の Ω 条件を備える実際の対象を使う。
使われ方：BF 1978 §2、HA §1.4.2、HTT 4.2.4.1 の Sp の空積。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 概要：点つき一点単体集合は Kan。
方針：基礎単体集合が終対象であることを使う。
規約：PointedObject.point の既存の定義を用いる。
使われ方：一点スペクトルの各段の Kan 条件。 -/
instance pointedPoint_kanComplex :
    KanComplex (PointedObject.point : PointedSimplicialSet.{u}).right := by
  change KanComplex (𝟙_ SSet.{u})
  apply kanComplex_of_rightHornFillers
  intro n i _ σ
  exact ⟨CartesianMonoidalCategory.isTerminalTensorUnit.from _,
    CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _⟩

/-- 概要：一点の懸垂は点つき単体集合の零対象。
方針：随伴によって一点からの射の一意性を移し、初対象として一点と同型にする。
規約：通常の smash による懸垂を使う。
使われ方：一点スペクトルの構造射の単射性。 -/
lemma suspensionPoint_isZero :
    IsZero (suspension (PointedObject.point : PointedSimplicialSet.{u})) := by
  have h : IsInitial (suspension (PointedObject.point : PointedSimplicialSet.{u})) :=
    IsInitial.ofUniqueHom (fun Y ↦ (suspensionLoopEquiv _ Y).symm 0)
      (fun Y f ↦ (suspensionLoopEquiv _ Y).injective (PointedObject.point_isZero.eq_of_src _ _))
  exact PointedObject.point_isZero.of_iso
    (h.uniqueUpToIso PointedObject.point_isZero.isInitial)

/-- 概要：一点の loop は点つき単体集合の零対象。
方針：随伴によって一点への射の一意性を移し、終対象として一点と同型にする。
規約：円からの点つき内部 Hom を使う。
使われ方：一点スペクトルの全基点の Ω 条件。 -/
lemma loopPoint_isZero :
    IsZero (loopSpace (PointedObject.point : PointedSimplicialSet.{u})) := by
  have h : IsTerminal (loopSpace (PointedObject.point : PointedSimplicialSet.{u})) :=
    IsTerminal.ofUniqueHom (fun Y ↦ suspensionLoopEquiv Y _ 0)
      (fun Y f ↦ (suspensionLoopEquiv Y _).symm.injective
        (PointedObject.point_isZero.eq_of_tgt _ _))
  exact PointedObject.point_isZero.of_iso
    (h.uniqueUpToIso PointedObject.point_isZero.isTerminal)

/-- 概要：各段が一点の実際の Ω スペクトル。
方針：懸垂構造射とその随伴が零対象間の同型であることを使う。
規約：全基点・零次数を含む Ω 条件と単射な構造射を持つ。
使われ方：BF 1978 §2、Sp の空積の頂点。 -/
def spectrumPoint : OmegaSpectrum.{u} where
  level _ := ⟨PointedObject.point, pointedPoint_kanComplex⟩
  sigma _ := PointedObject.toPoint _
  sigma_mono _ := by
    have := suspensionPoint_isZero.isIso PointedObject.point_isZero (PointedObject.toPoint _)
    change Mono (PointedSimplicialSet.forget.map (PointedObject.toPoint
      (suspension (PointedObject.point : PointedSimplicialSet.{u}))))
    infer_instance
  omega_condition _ := by
    let f := suspensionLoopEquiv (PointedObject.point : PointedSimplicialSet.{u}) _
      (PointedObject.toPoint _)
    have := PointedObject.point_isZero.isIso loopPoint_isZero f
    exact KanPiIsomorphism.of_iso (X := (PointedObject.point : PointedSimplicialSet.{u}).right)
      (Y := (loopSpace (PointedObject.point : PointedSimplicialSet.{u})).right)
      (PointedSimplicialSet.forget.mapIso (asIso f))

end
end SerrePositivity.InfinityCategories.HomotopyLimits
