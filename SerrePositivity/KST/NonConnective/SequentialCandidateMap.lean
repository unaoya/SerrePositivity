module
public import SerrePositivity.KST.NonConnective.SequentialLevelColimitLaws
public import SerrePositivity.KST.NonConnective.SequentialEdgePi
public import SerrePositivity.KST.LocalizingInvariants.SpectrumBFPiTransport

/-!
概要：元の逐次 BF 自然変換を、同じ実余極限候補間の比較へ渡す。
方針：元の段別余極限比較を、同じ BF 射影の hSp 同型で共役する。
規約：一般安定入力上の K 関手化や dg 入力作用の自然性は主張しない。
使われ方：K-7 の懸垂列の実比較が供給された後の Morita 比較の形式的利用側。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.NonConnective
local instance candidateMapSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance candidateMapHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

/-- 概要：同じ実候補から同じ段別余極限への元の BF 射影の hSp 同型。
方針：既証明の元の射影の全整数 π 同型性を使う。
規約：同型の順方向は元の射影そのものの類。
使われ方：元の逐次比較を同じ実候補へ移す。 -/
def sequentialCandidateProjectionIso (D : SpectrumSequence.{u}) :
    SpectrumHo.obj (sequentialSpectrum D) ≅ SpectrumHo.obj (sequentialLevelColimitSpectrum D) := by
  let p := SpectrumHo.hom (sequentialReplacementProjection D)
  have : IsIso p := OmegaSpectrum.isInvertible_of_piIsomorphism _
    (sequentialReplacementProjection_piIsomorphism D)
  exact asIso p

/-- 概要：同じ実逐次列自然変換から元の余極限候補間への hSp 比較。
方針：元の段別余極限射を同じ射影同型の順逆で挟む。
規約：各候補は既存の同じ BF 対象。
使われ方：K-7 の元の懸垂列の比較を実候補へ渡す。 -/
def sequentialCandidateHoMap {D E : SpectrumSequence.{u}} (η : D ⟶ E) :
    SpectrumHo.obj (sequentialSpectrum D) ⟶ SpectrumHo.obj (sequentialSpectrum E) :=
  (sequentialCandidateProjectionIso D).hom ≫
    SpectrumHo.hom (sequentialLevelColimitMap η) ≫ (sequentialCandidateProjectionIso E).inv

/-- 概要：元の恒等逐次比較は同じ実候補の hSp 恒等射。
方針：段別余極限の恒等則と同じ射影同型の両側逆を使う。
規約：BF 代表そのものの厳密恒等は主張しない。
使われ方：同じ実候補の hSp 関手則。 -/
theorem sequentialCandidateHoMap_id (D : SpectrumSequence.{u}) :
    sequentialCandidateHoMap (𝟙 D) = 𝟙 (SpectrumHo.obj (sequentialSpectrum D)) := by
  simp only [sequentialCandidateHoMap, sequentialLevelColimitMap_id,
    SpectrumHo.hom_id, Category.id_comp, Iso.hom_inv_id]

/-- 概要：元の逐次自然変換の合成は同じ候補の hSp 比較の合成。
方針：同じ段別余極限合成則と中央の射影同型の両側逆を使う。
規約：同じ実比較の類を保持する。
使われ方：同じ実候補の hSp 関手則。 -/
theorem sequentialCandidateHoMap_comp {D E F : SpectrumSequence.{u}}
    (η : D ⟶ E) (θ : E ⟶ F) :
    sequentialCandidateHoMap (η ≫ θ) = sequentialCandidateHoMap η ≫ sequentialCandidateHoMap θ := by
  simp only [sequentialCandidateHoMap, sequentialLevelColimitMap_comp, SpectrumHo.hom_comp,
    Category.assoc, Iso.inv_hom_id_assoc]

/-- 概要：元の厳密逐次 BF 列から同じ実候補の hSp への関手。
方針：元の射影を保持する比較の恒等・合成を使う。
規約：dg 入力や一般の安定 ∞ 圏上の K 関手ではなく、逐次列だけを始域とする。
使われ方：供給された実懸垂列比較を同じ非連結化候補へ送る形式部分。 -/
def sequentialCandidateHoFunctor : SpectrumSequence.{u} ⥤ hoFunctor.obj Sp.{u} where
  obj D := SpectrumHo.obj (sequentialSpectrum D)
  map := sequentialCandidateHoMap
  map_id := sequentialCandidateHoMap_id
  map_comp := sequentialCandidateHoMap_comp

/-- 概要：同じ hSp 比較を元の候補間の実 BF 射として読む。
方針：Sp 正本の元の端点を保つ代表を使う。
規約：代表の厳密な関手性や dg 入力自然性は主張しない。
使われ方：実候補間の比較の整数 π 作用と可逆性。 -/
def sequentialCandidateMap {D E : SpectrumSequence.{u}} (η : D ⟶ E) :
    sequentialSpectrum D ⟶ sequentialSpectrum E :=
  SpectrumHo.representative (sequentialCandidateHoMap η)

/-- 概要：読み戻した同じ BF 比較の hSp 類は元の候補比較そのもの。
方針：Sp 正本の代表の回収式を使う。
規約：元の端点と比較を保持する。
使われ方：元の実余極限の脚と整数 π の照合。 -/
theorem sequentialCandidateMap_hom {D E : SpectrumSequence.{u}} (η : D ⟶ E) :
    SpectrumHo.hom (sequentialCandidateMap η) = sequentialCandidateHoMap η :=
  SpectrumHo.hom_representative _

/-- 概要：同じ実候補比較は元の段別余極限比較と同じ射影の下で可換。
方針：同じ射影同型の逆と順方向を消去する。
規約：全整数 π だけでなく hSp の元の射の等式。
使われ方：元の実余極限の脚との可換性。 -/
theorem sequentialCandidateMap_projection {D E : SpectrumSequence.{u}} (η : D ⟶ E) :
    SpectrumHo.hom (sequentialCandidateMap η) ≫ SpectrumHo.hom (sequentialReplacementProjection E) =
      SpectrumHo.hom (sequentialReplacementProjection D) ≫
        SpectrumHo.hom (sequentialLevelColimitMap η) := by
  rw [sequentialCandidateMap_hom]
  change sequentialCandidateHoMap η ≫ (sequentialCandidateProjectionIso E).hom = _
  simp only [sequentialCandidateHoMap, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

end SerrePositivity.KST.NonConnective
