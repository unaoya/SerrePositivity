module

public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Frames.AffineCechVertexFrame
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Frames.BigCechFrameResidue
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Frames.BigCechFrameRetraction
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Frames.BigCechFrameComparison
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Frames.BigCechFrameResidue
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Frames.BigCechFrameRetraction

/-!
# 大きい prismatic 枠の頂点の普遍性と有限枠との比較

## 概要
同じ剰余環上に大小の枠を置き、比較の二つの合成を恒等射に結ぶ。

## 方針
大きい枠の剰余構造射を各変数から読み、既存の環射を剰余構造射つきの射に持ち上げる。
それぞれの始域の枠に、混合頂点のホモトピーを適用する。

## 規約
大きい枠の各項の有界性と、有限枠と共通の濃度上限を仮定に取る。

## 使われ方
BS 著者版 Remark 4.19 の枠比較。
-/

public noncomputable section

open CategoryTheory AlgebraicTopology
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic.BigCechVertexFrame

set_option backward.isDefEq.respectTransparency false

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)
variable (Q : Poly (A ⧸ P.ideal)) {κ : Cardinal.{u}}
variable (E : ∀ (Q' : Poly (A ⧸ P.ideal)) n, BigCechTerm P Q' n)
variable (hb : ∀ n, IsBoundedPrism (E Q n).prism)
variable (hκ : ∀ n, Cardinal.mk (E Q n).carrier ≤ κ)

local notation "R" => polyCompletion P Q.n
local notation "U₀" => PrismOver P R κ

private def term (n : ℕ) : U₀ where
  B := (E Q n).carrier
  Q := (E Q n).prism
  bounded := hb n
  toHom := (E Q n).base
  sec := (E Q n).residueSection
  sec_comp := (E Q n).residueSection_comp
  small := hκ n

private def hom {n : ℕ} {T : U₀} (f : (E Q n).carrier →+* T.B)
    (hd : (E Q n).prism.deltaStructure.IsDeltaHom T.Q.deltaStructure f)
    (hbase : f.comp (E Q n).base.toRingHom = T.toHom.toRingHom)
    (hv : ∀ s, Ideal.Quotient.mk T.Q.ideal (f ((E Q n).variableImage s)) = T.sec s.1) :
    term P Q E hb hκ n ⟶ T := by
  let F : OrientedPrism.Hom (E Q n).prism T.Q := ⟨f, hd, by
    rw [(E Q n).isEnvelope.ideal_eq, Ideal.span_singleton_le_iff_mem]
    change (f.comp (E Q n).base.toRingHom) P.generator ∈ T.Q.ideal
    rw [hbase]
    exact T.toHom.map_generator_mem⟩
  refine ⟨F, OrientedPrism.Hom.ext hbase, ?_⟩
  apply RingHom.ext
  intro a
  change F.quotientMap ((E Q n).residueSection a) = T.sec a
  rw [(E Q n).residueSection_variable (a, 0), OrientedPrism.Hom.quotientMap_mk]
  exact hv (a, 0)

private def map {m n : SimplexCategory} (θ : m ⟶ n) :
    term P Q E hb hκ m.len ⟶ term P Q E hb hκ n.len :=
  hom P Q E hb hκ ((E Q m.len).map (E Q n.len) (𝟙 Q) θ.toOrderHom)
    ((E Q m.len).map_isDeltaHom (E Q n.len) (𝟙 Q) θ.toOrderHom)
    ((E Q m.len).map_base (E Q n.len) (𝟙 Q) θ.toOrderHom) (by
      intro s
      change Ideal.Quotient.mk (E Q n.len).prism.ideal
        ((E Q m.len).map (E Q n.len) (𝟙 Q) θ.toOrderHom ((E Q m.len).variableImage s)) =
          (E Q n.len).residueSection s.1
      rw [BigCechTerm.map_variableImage, ← (E Q n.len).residueSection_variable]
      simp only [BigCechTerm.indexMap, polyCompletionMap_id, AlgHom.id_apply] <;> rfl)

/-- 大きい枠を剰余構造射つきの余単体的対象として読む。 -/
def model : CosimplicialObject U₀ where
  obj n := term P Q E hb hκ n.len
  map θ := map P Q E hb hκ θ
  map_id n := by
    apply PrismOver.Hom.ext
    apply OrientedPrism.Hom.ext
    exact (E Q n.len).map_id
  map_comp {l m n} θ η := by
    apply PrismOver.Hom.ext
    apply OrientedPrism.Hom.ext
    change (E Q l.len).map (E Q n.len) (𝟙 Q) (η.toOrderHom ∘ θ.toOrderHom) =
      ((E Q m.len).map (E Q n.len) (𝟙 Q) η.toOrderHom).comp
        ((E Q l.len).map (E Q m.len) (𝟙 Q) θ.toOrderHom)
    simpa only [Category.id_comp] using
      (E Q l.len).map_comp (E Q m.len) (E Q n.len) (𝟙 Q) θ.toOrderHom (𝟙 Q) η.toOrderHom

/-- 大きい枠の変数の普遍性。 -/
def vertexFrame : PrismOverVertexFrame P R κ (model P Q E hb hκ) R where
  residue := id
  variableImage n a i := (E Q n).variableImage (a, i)
  variable_mod n a i := ((E Q n).residueSection_variable (a, i)).symm
  variable_map {m n} θ a i := by
    change (E Q m).map (E Q n) (𝟙 Q) θ.toOrderHom ((E Q m).variableImage (a, i)) =
      (E Q n).variableImage (a, θ.toOrderHom i)
    rw [BigCechTerm.map_variableImage]
    simp only [BigCechTerm.indexMap, polyCompletionMap_id, AlgHom.id_apply]
  lift n T z hz := by
    obtain ⟨f, hf, hu⟩ := (E Q n).existsUnique_liftVariables T.Q T.toHom T.sec T.sec_comp
      (fun s => z s.1 s.2) (fun s => hz s.1 s.2)
    refine ⟨hom P Q E hb hκ f hf.1 hf.2.1
      (fun s => (congrArg (Ideal.Quotient.mk T.Q.ideal) (hf.2.2 s)).trans (hz s.1 s.2)),
      fun a i => hf.2.2 (a, i), ?_⟩
    intro g hg
    apply PrismOver.Hom.ext
    apply OrientedPrism.Hom.ext
    exact hu g.toHom.toRingHom ⟨g.toHom.map_delta,
      congrArg OrientedPrism.Hom.toRingHom g.comm_base, fun s => hg s.1 s.2⟩

variable (U : ∀ n, AffineEnvelopeTerm P Q.n n κ)

/-- 有限枠から大きい枠への比較。 -/
def toBig : (cechAlexanderOfAffineTerms P U) ⟶ model P Q E hb hκ where
  app n :=
    ⟨affineToBigPrismHom (U n.len) (E Q n.len),
      affineToBigPrismHom_base (U n.len) (E Q n.len),
      affineToBig_residueSection (U n.len) (E Q n.len)⟩
  naturality {m n} θ := by
    apply PrismOver.Hom.ext
    apply OrientedPrism.Hom.ext
    exact affineToBig_naturality U (E Q) θ

/-- 大きい枠から有限枠への、選んだ持ち上げに基づく比較。 -/
def toFinite : model P Q E hb hκ ⟶ (cechAlexanderOfAffineTerms P U) where
  app n := by
    let f := BigCechFrameRetraction.liftAt P Q U E n.len
    have hf := BigCechFrameRetraction.liftAt_spec P Q U E n.len
    refine hom P Q E hb hκ f hf.1 hf.2.1 ?_
    intro s
    change Ideal.Quotient.mk (U n.len).X.Q.ideal
      (BigCechFrameRetraction.liftAt P Q U E n.len ((E Q n.len).variableImage s)) =
        (U n.len).X.sec s.1
    rw [hf.2.2]
    exact BigCechFrameRetraction.values_mod P Q U n.len s
  naturality {m n} θ := by
    apply PrismOver.Hom.ext
    apply OrientedPrism.Hom.ext
    exact BigCechFrameRetraction.liftAt_naturality P Q U E θ

local notation "G" => prismSiteAlgebras P R κ ⋙ PDCechNerve.algebraModule A

/-- 有限枠での合成を恒等射に結ぶ余鎖ホモトピー。 -/
def finiteCompositeHomotopy :
    Homotopy
      ((alternatingCofaceMapComplex _).map
        (Functor.whiskerRight (toBig P Q E hb hκ U ≫ toFinite P Q E hb hκ U) G))
      ((alternatingCofaceMapComplex _).map
        (Functor.whiskerRight (𝟙 ((cechAlexanderOfAffineTerms P U))) G)) :=
  (affineCechVertexFrame P U).cochainHomotopy _ _

/-- 大きい枠での合成を恒等射に結ぶ余鎖ホモトピー。 -/
def bigCompositeHomotopy :
    Homotopy
      ((alternatingCofaceMapComplex _).map
        (Functor.whiskerRight (toFinite P Q E hb hκ U ≫ toBig P Q E hb hκ U) G))
      ((alternatingCofaceMapComplex _).map
        (Functor.whiskerRight (𝟙 (model P Q E hb hκ)) G)) :=
  (vertexFrame P Q E hb hκ).cochainHomotopy _ _

/-- 有限枠から大きい枠への比較は、交代余面複体で擬同型。 -/
theorem toBig_quasiIso :
    QuasiIso ((alternatingCofaceMapComplex _).map
      (Functor.whiskerRight (toBig P Q E hb hκ U) G)) := by
  let F := (Functor.whiskeringRight SimplexCategory _ _).obj G ⋙ alternatingCofaceMapComplex _
  let e : HomotopyEquiv (F.obj (cechAlexanderOfAffineTerms P U))
      (F.obj (model P Q E hb hκ)) :=
    { hom := F.map (toBig P Q E hb hκ U)
      inv := F.map (toFinite P Q E hb hκ U)
      homotopyHomInvId := by
        rw [← F.map_comp, ← F.map_id]
        exact finiteCompositeHomotopy P Q E hb hκ U
      homotopyInvHomId := by
        rw [← F.map_comp, ← F.map_id]
        exact bigCompositeHomotopy P Q E hb hκ U }
  exact e.quasiIso_hom

end SerrePositivity.BhattScholze.Prismatic.BigCechVertexFrame
