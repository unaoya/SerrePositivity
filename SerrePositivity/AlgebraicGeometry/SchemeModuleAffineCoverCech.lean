module

public import SerrePositivity.AlgebraicGeometry.SchemeModuleAffineCech
public import SerrePositivity.AlgebraicGeometry.SchemeCommonAffineCover
public import SerrePositivity.AlgebraicGeometry.SchemeFinitePrincipalRefinement
public import SerrePositivity.AlgebraicGeometry.OpenCoverCechRestrictedCover

/-!
概要：アフィン開集合のアフィン開被覆の、準連接係数の増大 Čech 完全性。
方針：有限標準細分を選び、正次数の行の縮約と交叉上の標準開の完全性を B1 に渡す。
規約：原典の導来関手の H との比較は作らない Čech 版。
使われ方：共通アフィン細分の cone の列の完全性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite _root_.AlgebraicGeometry
universe u
variable {Y : Scheme.{u}} (M : Y.Modules) [M.IsQuasicoherent]
variable {ι : Type} [LinearOrder ι] (W : Y.Opens) (hW : IsAffineOpen W)

include hW in
/-- アフィン標準開被覆の完全性を、増大項の単射性とともにまとめる。 -/
theorem schemeModuleStandardOpenCech_acyclic [Fintype ι] (f : ι → Γ(Y, W))
    (hspan : Ideal.span (Set.range f) = ⊤) :
    OpenCoverCechAcyclic (openCoverIntersectionPresheaf (schemeModuleCechPresheaf M) W)
      (fun i ↦ Y.basicOpen (f i)) where
  injective_zero := schemeModuleStandardOpenCech_zero_injective M W hW f hspan
  exact k := schemeModuleStandardOpenCech_exact M W hW f hspan k

include hW in
/-- アフィン標準開被覆の完全性は、小さいアフィン開への制限でも成り立つ。 -/
theorem schemeModuleStandardOpenCech_restrict [Fintype ι] (f : ι → Γ(Y, W))
    (hspan : Ideal.span (Set.range f) = ⊤) (Z : Y.Opens) (hZ : IsAffineOpen Z) (hZW : Z ≤ W) :
    OpenCoverCechAcyclic (openCoverIntersectionPresheaf (schemeModuleCechPresheaf M) Z)
      (fun i ↦ Y.basicOpen (f i)) := by
  let r := (Y.presheaf.map (homOfLE hZW).op).hom
  let g := fun i ↦ r (f i)
  have hg : Ideal.span (Set.range g) = ⊤ := by
    have h := congrArg (Ideal.map r) hspan
    simpa only [Ideal.map_span, Ideal.map_top, ← Set.range_comp, Function.comp_def, g] using h
  have hlocal := schemeModuleStandardOpenCech_acyclic M Z hZ g hg
  apply openCoverCechAcyclic_of_intersection_eq (schemeModuleCechPresheaf M) Z
    (fun i ↦ Y.basicOpen (g i)) (fun i ↦ Y.basicOpen (f i)) ?_ hlocal
  intro i
  have hgi : Y.basicOpen (g i) = Z ⊓ Y.basicOpen (f i) :=
    Y.basicOpen_res (f i) (homOfLE hZW).op
  rw [hgi, ← inf_assoc, inf_idem]

variable [IsAffineHom (pullback.diagonal (terminal.from Y))]

include hW in
/-- アフィン開集合をちょうど被覆するアフィン開被覆の増大 Čech 完全性。
原典 Stacks 30.2.6 のアフィン被覆による Hⁱ の消滅の Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem schemeModuleAffineCoverCech_acyclic (V : ι → Y.Opens)
    (hV : ∀ i, IsAffineOpen (V i)) (hcover : (⨆ i, V i) = W) :
    OpenCoverCechAcyclic (openCoverIntersectionPresheaf (schemeModuleCechPresheaf M) W) V := by
  obtain ⟨n, f, ρ, hspan, hρ⟩ := schemeFinitePrincipalRefinement W hW V hcover
  let U := fun i ↦ Y.basicOpen (f i)
  apply openCoverCechAcyclic_of_refinement
    (openCoverIntersectionPresheaf (schemeModuleCechPresheaf M) W) V U ρ hρ
    (schemeModuleStandardOpenCech_acyclic M W hW f hspan)
  intro i hi t
  let Z := cechOpenIntersection V (cechTupleSupport t)
  have hnonempty : (cechTupleSupport t).Nonempty :=
    ⟨t ⟨0, hi⟩, Finset.mem_image.mpr ⟨⟨0, hi⟩, Finset.mem_univ _, rfl⟩⟩
  have hZ : IsAffineOpen Z := cechOpenIntersection_isAffineOpen V hV _ hnonempty
  have hZW : Z ≤ W := by
    apply (cechOpenIntersection_le_tuple_member V t ⟨0, hi⟩).trans
    rw [← hcover]
    exact le_iSup V (t ⟨0, hi⟩)
  have hlocal := schemeModuleStandardOpenCech_restrict M W hW f hspan Z hZ hZW
  exact openCoverCechAcyclic_of_iso
    (openCoverIntersectionPresheaf (schemeModuleCechPresheaf M) Z) U
    (openCoverIntersectionPresheafNestedIsoOfLe (schemeModuleCechPresheaf M) W Z hZW).symm hlocal

include hW in
/-- アフィン開と各被覆開との交叉がアフィンで、その開を被覆すれば、増大 Čech は完全。
原典 Stacks 30.2.6 のアフィン交叉上の Hⁱ の消滅の Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem schemeModuleAffineOpenCech_acyclic (V : ι → Y.Opens)
    (hV : ∀ i, IsAffineOpen (W ⊓ V i)) (hcover : W ≤ ⨆ i, V i) :
    OpenCoverCechAcyclic (openCoverIntersectionPresheaf (schemeModuleCechPresheaf M) W) V := by
  let V' := fun i ↦ W ⊓ V i
  have hc : (⨆ i, V' i) = W := by
    apply le_antisymm
    · exact iSup_le fun i ↦ inf_le_left
    · intro x hx
      obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover hx)
      exact Opens.mem_iSup.mpr ⟨i, ⟨hx, hi⟩⟩
  have hlocal := schemeModuleAffineCoverCech_acyclic M W hW V' hV hc
  apply openCoverCechAcyclic_of_intersection_eq (schemeModuleCechPresheaf M) W V' V ?_ hlocal
  intro i
  change W ⊓ (W ⊓ V i) = W ⊓ V i
  rw [← inf_assoc, inf_idem]

end SerrePositivity.AlgebraicGeometry
