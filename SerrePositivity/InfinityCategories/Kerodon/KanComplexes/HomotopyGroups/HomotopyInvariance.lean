module


public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyDegreeZero
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-!
概要：境界を固定した単体のホモトピーをホモトピー類の等式へ送る。
方針：標準 prism を三角形分割し、各単体を RelStruct として読む。
規約：正次数の単体を扱い、基点はホモトピーの全区間で固定する。
使われ方：Kerodon §§3.2.1（Tag 00V4）–3.2.3（Tag 00W3）、Goerss–Jardine I §7。L9a の不変性。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u

open CategoryTheory SSet MonoidalCategory CartesianMonoidalCategory
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Spectra.RelativePrism
end SerrePositivity.KST.Spectra.RelativePrism
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open _root_.SerrePositivity.KST.Spectra

namespace RelativePrism
open _root_.SerrePositivity.KST.Spectra.RelativePrism

variable {X : SSet.{u}} {n : ℕ} {x : X _⦋0⦌}
  {f g : X.PtSimplex (n + 1) x} (H : f.Homotopy g)

/-- 概要：標準 prism の対角断面の第一射影は恒等射。
方針：Yoneda の対応で第一成分を計算する。
規約：断面の添字は零頂点の個数。
使われ方：Kerodon §3.2.3（Tag 00W3）。境界条件の確認。 -/
@[reassoc (attr := simp)]
theorem codim_fst (i : Fin (n + 3)) :
    yonedaEquiv.symm (prodStdSimplex₁.codimOneSimplex.{u} i).val ≫ fst _ _ =
      𝟙 (Δ[n + 1] : SSet.{u}) := by
  apply yonedaEquiv.injective
  rfl

/-- 概要：prism の第一射影が境界を経由する単体は基点に定数。
方針：境界の prism へ因子化し、相対ホモトピーの固定条件を使う。
規約：q の次数 m は任意。
使われ方：Kerodon Proposition 3.2.1.4（Tag 00V9）。三角形分割の外側の面。 -/
theorem boundary_constant {m : ℕ} (q : (Δ[m] : SSet.{u}) ⟶ Δ[n + 1] ⊗ Δ[1])
    (j : Fin (n + 2)) (a : (Δ[m] : SSet.{u}) ⟶ Δ[n])
    (hq : q ≫ fst _ _ = a ≫ stdSimplex.δ j) : q ≫ H.h = SSet.const x := by
  have hfactor : q = lift (a ≫ boundary.ι j) (q ≫ snd _ _) ≫ (boundary (n + 1)).ι ▷ Δ[1] := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [hq]
  rw [hfactor, Category.assoc, H.rel]
  simp

/-- 概要：prism の対角断面から境界定数単体を作る。
方針：第一射影が恒等射の標準断面をホモトピーに代入する。
規約：i は零を取る頂点の個数。
使われ方：Kerodon §3.2.3（Tag 00W3）。相対ホモトピーから RelStruct の列への変換。 -/
noncomputable def sectionSimplex (i : Fin (n + 3)) : X.PtSimplex (n + 1) x where
  map := yonedaEquiv.symm (prodStdSimplex₁.codimOneSimplex i).val ≫ H.h
  comm := by
    ext j : 1
    simp only [boundary.ι_ι_assoc, Subcomplex.ofSimplex_ι, comp_const]
    rw [← Category.assoc]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.RelativePrism.boundary_constant H _ j (𝟙 _)
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.RelativePrism.codim_fst, Category.comp_id, Category.id_comp]

/-- 概要：三角形分割の各 prism 単体の第一射影は退化写像。
方針：標準 prism の列挙の第一成分を Yoneda で読む。
規約：i は重複する頂点。
使われ方：Kerodon §3.2.3（Tag 00W3）。RelStruct の定数面の検証。 -/
theorem prism_fst (i : Fin (n + 2)) :
    yonedaEquiv.symm (prodStdSimplex₁.nonDegenerateEquiv.{u} i).val ≫ fst _ _ =
      stdSimplex.σ i := by
  apply yonedaEquiv.injective
  rfl

/-- 概要：隣接する対角断面の間に RelStruct がある。
方針：prism の三角形分割の一単体を取り、外側の面は境界経由で定数と示す。
規約：RelStruct の面添字は重複頂点の位置。
使われ方：Kerodon §3.2.3（Tag 00W3）。ホモトピー類の不変性。 -/
noncomputable def sectionRel (i : Fin (n + 2)) :
    PtSimplex.RelStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.RelativePrism.sectionSimplex H i.castSucc) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.RelativePrism.sectionSimplex H i.succ) i where
  map := yonedaEquiv.symm (prodStdSimplex₁.nonDegenerateEquiv i).val ≫ H.h
  δ_castSucc_map := by
    rw [← Category.assoc, stdSimplex.δ_comp_yonedaEquiv_symm,
      prodStdSimplex₁.δ_castSucc_nonDegenerateEquiv]
    rfl
  δ_succ_map := by
    rw [← Category.assoc, stdSimplex.δ_comp_yonedaEquiv_symm,
      prodStdSimplex₁.δ_succ_nonDegenerateEquiv]
    rfl
  δ_map_of_lt j hj := by
    obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero (by grind : i ≠ 0)
    obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hj)
    rw [← Category.assoc]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.RelativePrism.boundary_constant H _ j (stdSimplex.σ i)
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.RelativePrism.prism_fst]
    exact stdSimplex.δ_comp_σ_of_le (by grind)
  δ_map_of_gt j hj := by
    obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last (by grind : i ≠ Fin.last (n + 1))
    obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hj)
    rw [← Category.assoc]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.RelativePrism.boundary_constant H _ j (stdSimplex.σ i)
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.RelativePrism.prism_fst]
    exact stdSimplex.δ_comp_σ_of_gt (by grind)

/-- 概要：零番目の断面はホモトピーの終点。
方針：区間成分が全頂点で一であることを計算する。
規約：prism の断面添字は零頂点の個数。
使われ方：Kerodon §3.2.3（Tag 00W3）。断面列の端点。 -/
theorem sectionSimplex_zero : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.RelativePrism.sectionSimplex H 0 = g := by
  have he : yonedaEquiv.symm (prodStdSimplex₁.codimOneSimplex.{u}
      (p := n + 1) 0).val = ι₁ := by
    apply yonedaEquiv.injective
    apply Prod.ext
    · rfl
    · change stdSimplex.objMk₁ 0 =
        (ι₁.app _ (yonedaEquiv (𝟙 (Δ[n + 1] : SSet.{u})))).2
      ext k : 1
      simp [stdSimplex.objMk₁_apply, ι₁_app_snd_apply]
  ext : 1
  change yonedaEquiv.symm _ ≫ H.h = g.map
  rw [he, H.h₁]

/-- 概要：最後の断面はホモトピーの始点。
方針：区間成分が全頂点で零であることを計算する。
規約：正次数の単体の全頂点を零側に置く。
使われ方：Kerodon §3.2.3（Tag 00W3）。断面列の端点。 -/
theorem sectionSimplex_last : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.RelativePrism.sectionSimplex H (Fin.last (n + 2)) = f := by
  have he : yonedaEquiv.symm (prodStdSimplex₁.codimOneSimplex.{u}
      (p := n + 1) (Fin.last (n + 2))).val = ι₀ := by
    apply yonedaEquiv.injective
    apply Prod.ext
    · rfl
    · change stdSimplex.objMk₁ (Fin.last (n + 2)) =
        (ι₀.app _ (yonedaEquiv (𝟙 (Δ[n + 1] : SSet.{u})))).2
      ext k : 1
      simp [stdSimplex.objMk₁_apply, ι₀_app_snd_apply]
  ext : 1
  change yonedaEquiv.symm _ ≫ H.h = f.map
  rw [he, H.h₀]

/-- 概要：prism の全断面は同じホモトピー類を持つ。
方針：隣接断面間の RelStruct の列に沿って帰納する。
規約：標的は Kan 複体。
使われ方：Kerodon §3.2.3（Tag 00W3）。相対ホモトピーによる不変性。 -/
theorem section_class_eq_zero [KanComplex X] (i : Fin (n + 3)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.RelativePrism.sectionSimplex H i) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.RelativePrism.sectionSimplex H 0) := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih => exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.sound (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.RelativePrism.sectionRel H i)).symm.trans ih

end RelativePrism

/-- 概要：境界を固定してホモトピックな代表単体は同じ類を持つ。
方針：prism の断面列を RelStruct によりつなぐ。
規約：正次数で、ホモトピーは基点上に定数。
使われ方：Kerodon Proposition 3.2.1.4（Tag 00V9） と §3.2.3。L9a のホモトピー不変性。 -/
theorem KanHomotopyGroup.eq_of_relativeHomotopy {X : SSet.{u}} [KanComplex X]
    {n : ℕ} {x : X _⦋0⦌} {f g : X.PtSimplex (n + 1) x} (H : f.Homotopy g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk f = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk g := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.RelativePrism.sectionSimplex_last, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.RelativePrism.sectionSimplex_zero] using
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.RelativePrism.section_class_eq_zero H (Fin.last (n + 2))

/-- 概要：基点を固定するホモトピーの両端は同じ群準同型を誘導する。
方針：代表単体を相対ホモトピーへ前合成し、類の等式を使う。
規約：両端の射は x を同じ y に送り、全区間で基点を固定する。
使われ方：Kerodon Proposition 3.2.1.4（Tag 00V9） と §3.2.2。π_n のホモトピー不変性。 -/
theorem KanHomotopyGroup.map_eq_of_basedHomotopy {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] {n : ℕ} {x : X _⦋0⦌} {y : Y _⦋0⦌}
    {φ ψ : X ⟶ Y} (hφ : φ.app _ x = y) (hψ : ψ.app _ x = y)
    (H : (RelativeMorphism.ofSimplex₀ φ x y hφ).Homotopy
      (RelativeMorphism.ofSimplex₀ ψ x y hψ)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := n) φ hφ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map ψ hψ := by
  ext a
  induction a using Quotient.inductionOn with | h s => ?_
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex φ hφ s) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex ψ hψ s)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.eq_of_relativeHomotopy
  exact H.precomp s (by simp)

/-- 概要：基点付きホモトピー逆を持つ射はホモトピー群の同型を誘導する。
方針：合成の保存と基点固定ホモトピーの不変性から両逆の法則を得る。
規約：二つの合成の基点保存を明示し、逆の法則は実際の相対ホモトピーで与える。
使われ方：Kerodon Proposition 3.2.1.13（Tag 00WW） と §3.2.2。置換による π_* の保存。 -/
noncomputable def KanHomotopyGroup.equivOfBasedHomotopyInverse {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] {n : ℕ} {x : X _⦋0⦌} {y : Y _⦋0⦌}
    (φ : X ⟶ Y) (ψ : Y ⟶ X) (hφ : φ.app _ x = y) (hψ : ψ.app _ y = x)
    (hφψ : (φ ≫ ψ).app _ x = x) (hψφ : (ψ ≫ φ).app _ y = y)
    (Hleft : (RelativeMorphism.ofSimplex₀ (φ ≫ ψ) x x hφψ).Homotopy
      (RelativeMorphism.ofSimplex₀ (𝟙 X) x x rfl))
    (Hright : (RelativeMorphism.ofSimplex₀ (ψ ≫ φ) y y hψφ).Homotopy
      (RelativeMorphism.ofSimplex₀ (𝟙 Y) y y rfl)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x ≃* _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y n y where
  toFun := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map φ hφ
  invFun := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map ψ hψ
  left_inv a := by
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_eq_of_basedHomotopy (n := n) hφψ rfl Hleft
    have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_comp (n := n) φ hφ ψ hψ hφψ
    exact DFunLike.congr_fun (hc.symm.trans (h.trans _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_id)) a
  right_inv a := by
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_eq_of_basedHomotopy (n := n) hψφ rfl Hright
    have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_comp (n := n) ψ hψ φ hφ hψφ
    exact DFunLike.congr_fun (hc.symm.trans (h.trans _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_id)) a
  map_mul' a b := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map φ hφ).map_mul a b

/-- 概要：ホモトピックな射は連結成分上で同じ写像を誘導する。
方針：各頂点の prism の辺を取って連結成分の等式を得る。
規約：この零次数の結論には Kan 性も基点固定も不要。
使われ方：Kerodon §3.2.1（Tag 00V4）、Example 3.2.2.6（Tag 00VQ）。零次数の不変性。 -/
theorem mapPiZero_eq_of_homotopy {X Y : SSet.{u}} {φ ψ : X ⟶ Y}
    (H : SSet.Homotopy φ ψ) (a : π₀ X) : mapπ₀ φ a = mapπ₀ ψ a := by
  induction a using π₀.rec with | mk v => ?_
  let C := H.toSimplicialObjectHomotopy
  apply π₀.sound
  refine SSet.Edge.mk (C.h 0 v) ?_ ?_
  · exact congr($(C.h_last_comp_δ_last 0) v)
  · exact congr($(C.h_zero_comp_δ_zero 0) v)

/-- 概要：基点を保つ射のホモトピーは零次数の誘導写像の等式を与える。
方針：π₀ との自然な全単射を通じて頂点の辺の計算を使う。
規約：hφ、hψ は同じ基点 y への像を指定する。
使われ方：Kerodon Example 3.2.2.6（Tag 00VQ）。全次数のホモトピー不変性。 -/
theorem KanHomotopyZero.map_eq_of_homotopy {X Y : SSet.{u}}
    {x : X _⦋0⦌} {y : Y _⦋0⦌} {φ ψ : X ⟶ Y}
    (hφ : φ.app _ x = y) (hψ : ψ.app _ x = y) (H : SSet.Homotopy φ ψ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero X x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.map φ hφ a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.map ψ hψ a := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero.injective
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero_map] using _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapPiZero_eq_of_homotopy H _

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
