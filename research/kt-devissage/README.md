# G₀ の dévissage（ビルドの対象外）

KTheory/Devissage* の 7 本（654 行）。台つき G₀ の dévissage（素イデアル商の類による生成と、その独立性・逆写像）を与えるが、
論文の主経路からも他のファイルからも使われていなかったので、2026-11-01 の決定（refactor-plan §6.2.1）でビルドの対象から外してここに退避した。
Paper/Section5/ModuleReduction が使うのは別物の IntersectionMultiplicity の dévissage。

再び使うときは `SerrePositivity/KTheory/` へ戻し、import 行を区切り 1-4 の後のモジュール名（例：`KTheory.G0.Basic`・`KTheory.K0LocalizationCoefficients`）に
合わせる。DevissageAnnihilated の `KTheory.K0LocalizationCoefficients` への import は不要な依存だった。
