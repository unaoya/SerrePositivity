module

public import SerrePositivity.KST.Spectra.PointedIntervalAnodyne
public import SerrePositivity.Spectra.PointedSimplicialSet.AdjoinBasepointUnit
public import SerrePositivity.HomotopicalAlgebra.Simplicial.Generators

/-!
概要：自由な基点を加えた区間と二つの端点の包含。
方針：零次単体の面の anodyne 性を、基点との余積と単位の同型へ移す。
規約：面添字一が時刻零、面添字零が時刻一。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HTT A.3.3。任意の射の mapping path 置換。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SSet.modelCategoryQuillen
open SerrePositivity.SimplicialModel
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：anodyne な単体集合の射は単射。
方針：全ての単射への RLP はホーンへの RLP を含み、境界生成の左クラスへ移す。
規約：モデル構造の弱同値の公理は用いない。
使われ方：Goerss–Jardine I §7、HTT A.3.3。自由な端点包含の単射性。 -/
theorem anodyne_mono {A B : SSet.{u}} (i : A ⟶ B) (hi : anodyneExtensions i) : Mono i := by
  have h : I.rlp.llp i := by
    intro E Z p hp
    have hp' : (MorphismProperty.monomorphisms SSet.{u}).rlp p := by
      rw [SSet.rlp_monomorphisms]
      exact hp
    exact hi p (fun _ _ j hj ↦ hp' j (J_le_monomorphisms _ hj))
  rw [boundaryGenerators_leftClass] at h
  exact h

/-- 概要：単射と恒等射の余積は単射。
方針：境界生成の左クラスの押し出しに関する閉性を使う。
規約：単体集合の射について述べる。
使われ方：Goerss–Jardine I §7、HTT A.3.3。基点を追加した区間の境界。 -/
theorem mono_coprod_map_id {A B C : SSet.{u}} (i : A ⟶ B) [Mono i] :
    Mono (coprod.map i (𝟙 C)) := by
  have hi : I.rlp.llp i := by
    rw [boundaryGenerators_leftClass]
    infer_instance
  have h := I.rlp.llp.of_isPushout (IsPushout.of_coprod_inl_with_id i C) hi
  rw [boundaryGenerators_leftClass] at h
  exact h

/-- 概要：anodyne 射と恒等射との余積も anodyne。
方針：元の成分の持ち上げと、新しい成分で既存の射をそのまま使う。
規約：余積の第二成分は任意の単体集合 C。
使われ方：Goerss–Jardine I §7、HTT A.3.3。基点追加による端点の充填の保存。 -/
theorem anodyne_coprod_map_id {A B C : SSet.{u}} (i : A ⟶ B)
    (hi : anodyneExtensions i) : anodyneExtensions (coprod.map i (𝟙 C)) := by
  intro E Z p hp
  let : HasLiftingProperty i p := hi p hp
  constructor
  intro a b sq
  let sq' : CommSq ((coprod.inl : A ⟶ A ⨿ C) ≫ a) i p
      ((coprod.inl : B ⟶ B ⨿ C) ≫ b) := by
    constructor
    have h := congrArg (fun k : A ⨿ C ⟶ Z ↦ (coprod.inl : A ⟶ A ⨿ C) ≫ k) sq.w
    simpa only [Category.assoc, coprod.inl_map_assoc] using h
  have hC : (coprod.inr : C ⟶ A ⨿ C) ≫ a ≫ p = (coprod.inr : C ⟶ B ⨿ C) ≫ b := by
    have h := congrArg (fun k : A ⨿ C ⟶ Z ↦ (coprod.inr : C ⟶ A ⨿ C) ≫ k) sq.w
    simpa only [Category.assoc, coprod.inr_map_assoc, Category.id_comp] using h
  let l := coprod.desc sq'.lift ((coprod.inr : C ⟶ A ⨿ C) ≫ a)
  refine ⟨⟨{ l := l, fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply coprod.hom_ext
    · simp only [l, coprod.inl_map_assoc, coprod.inl_desc, sq'.fac_left]
    · simp only [l, coprod.inr_map_assoc, coprod.inr_desc, Category.id_comp]
  · apply coprod.hom_ext
    · simp only [l, coprod.inl_desc_assoc, sq'.fac_right]
    · simpa only [l, coprod.inr_desc_assoc, Category.assoc] using hC

/-- 概要：一次ホーン Λ[1,1] は時刻一の面。
方針：残る面が零だけであることを有限添字で検査する。
規約：面添字は零、頂点の値は一。
使われ方：Kerodon §3.1.1、Goerss–Jardine I §7。もう一方の端点の充填。 -/
theorem horn_one_one_eq_face : (horn.{u} 1 1) = stdSimplex.face {(0 : Fin 2)}ᶜ := by
  rw [horn_eq_iSup]
  apply le_antisymm
  · apply iSup_le
    intro j
    have hj0 : j.val = 0 := by
      by_contra h
      exact j.property (Fin.eq_one_of_ne_zero j.val h)
    simpa only [hj0] using (le_refl (stdSimplex.face {(0 : Fin 2)}ᶜ : (Δ[1] : SSet.{u}).Subcomplex))
  · exact le_iSup_of_le ⟨0, by decide⟩ le_rfl

/-- 概要：区間の時刻一の包含も anodyne。
方針：一次ホーンと零の面の標準同型で移す。
規約：射は Δ[0] から Δ[1] への δ₀。
使われ方：Kerodon §3.1.1、Goerss–Jardine I §7。自由な path の端点評価。 -/
theorem interval_oneFace_anodyne : anodyneExtensions (stdSimplex.δ.{u} (0 : Fin 2)) := by
  have hh : anodyneExtensions (stdSimplex.face.{u} {(0 : Fin 2)}ᶜ).ι := by
    rw [← horn_one_one_eq_face]
    exact anodyneExtensions.horn_ι 1
  rw [← stdSimplex.faceSingletonComplIso_hom_ι (0 : Fin 2)]
  exact anodyneExtensions.comp_mem _ _ (anodyneExtensions.of_isIso _) hh

/-- 概要：区間の二つの零次面はどちらも anodyne。
方針：二つの添字で場合分けする。
規約：面の添字は頂点の値と逆。
使われ方：Goerss–Jardine I §7。自由な端点包含の共通の界面。 -/
theorem intervalFace_anodyne (i : Fin 2) : anodyneExtensions (stdSimplex.δ.{u} i) := by
  fin_cases i
  · exact interval_oneFace_anodyne
  · exact interval_zeroFace_anodyne

/-- 概要：自由な基点を別成分として加えた区間。
方針：既存の基点追加の関手を使う。
規約：区間の端点自体は新しい基点ではない。
使われ方：Goerss–Jardine I §7、BF 1978 §2。自由な path のパラメータ。 -/
def freeInterval : PointedSimplicialSet.{u} :=
  PointedSimplicialSet.adjoinBasepoint (Δ[1] : SSet.{u})

/-- 概要：smash の単位から自由な区間への端点の射。
方針：零次単体の基点追加と単位の同型を面の基点追加へ前合成する。
規約：i=1 は時刻零、i=0 は時刻一。
使われ方：Goerss–Jardine I §7。自由な path の二つの評価。 -/
def freeIntervalEndpoint (i : Fin 2) : 𝟙_ PointedSimplicialSet.{u} ⟶ freeInterval.{u} :=
  PointedSimplicialSet.adjoinBasepointDeltaZeroIso.inv ≫
    PointedSimplicialSet.adjoinBasepointFunctor.map (stdSimplex.δ i)

/-- 概要：自由な区間の端点包含の基礎射は anodyne。
方針：零次面と基点の恒等射との余積、単位同型との合成を使う。
規約：両方の端点を含む。
使われ方：Goerss–Jardine I §7、HTT A.3.3。端点評価の全境界充填。 -/
theorem freeIntervalEndpoint_anodyne (i : Fin 2) :
    anodyneExtensions (freeIntervalEndpoint.{u} i).right := by
  change anodyneExtensions
    (PointedSimplicialSet.adjoinBasepointDeltaZeroIso.inv.right ≫
      coprod.map (stdSimplex.δ i) (𝟙 (𝟙_ SSet.{u})))
  exact anodyneExtensions.comp_mem _ _ (anodyneExtensions.of_isIso _)
    (anodyne_coprod_map_id _ (intervalFace_anodyne i))

/-- 概要：自由な区間の端点包含は単射。
方針：証明済みの anodyne 射の単射性を使う。
規約：基礎単体集合の射について述べる。
使われ方：Kerodon §3.1.3、Goerss–Jardine I §7。端点評価の Kan fibration 性。 -/
instance freeIntervalEndpoint_mono (i : Fin 2) : Mono (freeIntervalEndpoint.{u} i).right :=
  anodyne_mono _ (freeIntervalEndpoint_anodyne i)

/-- 概要：自由な区間を smash の単位へ潰す点つき射。
方針：区間から終単体集合への射に基点を加える。
規約：区間全体を単位の非基点へ送る。
使われ方：Goerss–Jardine I §7。定数 path の射の定義。 -/
def freeIntervalCollapse : freeInterval.{u} ⟶ 𝟙_ PointedSimplicialSet.{u} :=
  PointedSimplicialSet.adjoinBasepointFunctor.map (toUnit (Δ[1] : SSet.{u})) ≫
    PointedSimplicialSet.adjoinBasepointUnitIso.hom

/-- 概要：端点を自由な区間へ入れて潰すと単位の恒等射。
方針：終単体集合への射の一意性と零次単体の単位同型の逆関係を使う。
規約：両方の端点で同じ式。
使われ方：Goerss–Jardine I §7。定数 path の二つの端点の計算。 -/
@[reassoc (attr := simp)]
theorem freeIntervalEndpoint_collapse (i : Fin 2) :
    freeIntervalEndpoint.{u} i ≫ freeIntervalCollapse = 𝟙 _ := by
  have h : stdSimplex.δ.{u} i ≫ toUnit (Δ[1] : SSet.{u}) =
      PointedSimplicialSet.deltaZeroUnitIso.hom := isTerminalTensorUnit.hom_ext _ _
  unfold freeIntervalEndpoint freeIntervalCollapse
  rw [Category.assoc, ← Category.assoc
    (PointedSimplicialSet.adjoinBasepointFunctor.map (stdSimplex.δ i))
    (PointedSimplicialSet.adjoinBasepointFunctor.map (toUnit (Δ[1] : SSet.{u})))
    PointedSimplicialSet.adjoinBasepointUnitIso.hom, ← Functor.map_comp, h]
  exact PointedSimplicialSet.adjoinBasepointDeltaZeroIso.inv_hom_id

end

end SerrePositivity.KST.Spectra
