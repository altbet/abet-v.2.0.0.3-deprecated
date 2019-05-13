// Copyright (c) 2011-2014 The Bitcoin developers
// Copyright (c) 2014-2015 The Dash developers
// Copyright (c) 2015-2017 The PIVX developers
// Copyright (c) 2018-2019 The Phore Developers
// Copyright (c) 2019 The Altbet Developers
// Distributed under the MIT/X11 software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "overviewpage.h"
#include "ui_overviewpage.h"

#include "bitcoinunits.h"
#include "clientmodel.h"
#include "guiconstants.h"
#include "guiutil.h"
#include "init.h"
#include "obfuscation.h"
#include "obfuscationconfig.h"
#include "optionsmodel.h"
#include "transactionfilterproxy.h"
#include "transactionrecord.h"
#include "transactiontablemodel.h"
#include "walletmodel.h"
#include "masternodeman.h"
#include "walletmodel.h"
#include "rpcblockchain.cpp"
#include "chainparams.h"
#include "chainparams.h"

#include <QAbstractItemDelegate>
#include <QPainter>
#include <QSettings>
#include <QTimer>
#include <QNetworkAccessManager>
#include <QNetworkRequest>
#include <QNetworkReply>
#include <QUrl>
#include <QBuffer>
#include <QDesktopServices>

#define DECORATION_SIZE 68
#define ICON_OFFSET 16
#define NUM_ITEMS 9

extern CWallet* pwalletMain;

extern CWallet* pwalletMain;

class TxViewDelegate : public QAbstractItemDelegate
{
    Q_OBJECT
public:
    TxViewDelegate() : QAbstractItemDelegate(), unit(BitcoinUnits::ABET)
    {
    }

    inline void paint(QPainter* painter, const QStyleOptionViewItem& option, const QModelIndex& index) const
    {
        painter->save();

        QIcon icon = qvariant_cast<QIcon>(index.data(Qt::DecorationRole));
        QRect mainRect = option.rect;
        mainRect.moveLeft(ICON_OFFSET);
        QRect decorationRect(mainRect.topLeft(), QSize(DECORATION_SIZE, DECORATION_SIZE));
        decorationRect.setWidth(595);
        int xspace = DECORATION_SIZE + 8;
        int ypad = 6;
        int halfheight = (mainRect.height() - 2 * ypad) / 2;
        QRect amountRect(mainRect.left() + xspace, mainRect.top() + ypad, mainRect.width() - xspace - ICON_OFFSET, halfheight);
        QRect addressRect(mainRect.left() + xspace, mainRect.top() + ypad + halfheight, mainRect.width() - xspace, halfheight);
        icon.paint(painter, decorationRect);

        QDateTime date = index.data(TransactionTableModel::DateRole).toDateTime();
        QString address = index.data(Qt::DisplayRole).toString();
        qint64 amount = index.data(TransactionTableModel::AmountRole).toLongLong();
        bool confirmed = index.data(TransactionTableModel::ConfirmedRole).toBool();

        // Check transaction status
        int nStatus = index.data(TransactionTableModel::StatusRole).toInt();
        bool fConflicted = false;
        if (nStatus == TransactionStatus::Conflicted || nStatus == TransactionStatus::NotAccepted) {
            fConflicted = true; // Most probably orphaned, but could have other reasons as well
        }
        bool fImmature = false;
        if (nStatus == TransactionStatus::Immature) {
            fImmature = true;
        }

        QVariant value = index.data(Qt::ForegroundRole);
        QColor foreground = COLOR_BLACK;
        if (value.canConvert<QBrush>()) {
            QBrush brush = qvariant_cast<QBrush>(value);
            foreground = brush.color();
        }

        painter->setPen(foreground);
        QRect boundingRect;
        painter->drawText(addressRect, Qt::AlignLeft | Qt::AlignVCenter, address, &boundingRect);

        if (index.data(TransactionTableModel::WatchonlyRole).toBool()) {
            QIcon iconWatchonly = qvariant_cast<QIcon>(index.data(TransactionTableModel::WatchonlyDecorationRole));
            QRect watchonlyRect(boundingRect.right() + 5, mainRect.top() + ypad + halfheight, 16, halfheight);
            iconWatchonly.paint(painter, watchonlyRect);
        }

        if(fConflicted) { // No need to check anything else for conflicted transactions
            foreground = COLOR_CONFLICTED;
        } else if (!confirmed || fImmature) {
            foreground = COLOR_UNCONFIRMED;
        } else if (amount < 0) {
            foreground = COLOR_NEGATIVE;
        } else {
            foreground = COLOR_BLACK;
        }
        painter->setPen(foreground);
        QString amountText = BitcoinUnits::formatWithUnit(unit, amount, true, BitcoinUnits::separatorAlways);
        if (!confirmed) {
            amountText = QString("[") + amountText + QString("]");
        }
        painter->drawText(amountRect, Qt::AlignRight | Qt::AlignVCenter, amountText);

        painter->setPen(foreground);
        painter->drawText(amountRect, Qt::AlignLeft | Qt::AlignVCenter, GUIUtil::dateTimeStr(date));

        painter->restore();
    }

    inline QSize sizeHint(const QStyleOptionViewItem& option, const QModelIndex& index) const
    {
        return QSize(DECORATION_SIZE, DECORATION_SIZE);
    }

    int unit;
};
#include "overviewpage.moc"

OverviewPage::OverviewPage(QWidget* parent) : QWidget(parent),
                                              ui(new Ui::OverviewPage),
                                              clientModel(0),
                                              walletModel(0),
                                              currentBalance(-1),
                                              currentUnconfirmedBalance(-1),
                                              currentImmatureBalance(-1),
                                              currentWatchOnlyBalance(-1),
                                              currentWatchUnconfBalance(-1),
                                              currentWatchImmatureBalance(-1),
                                              txdelegate(new TxViewDelegate()),
                                              filter(0)
{
    nDisplayUnit = 0; // just make sure it's not unitialized
    ui->setupUi(this);

	/*
	ui->pushButton_Website->setIcon(QIcon(":/icons/website"));
	ui->pushButton_Discord->setIcon(QIcon(":/icons/discord"));
	ui->pushButton_Github->setIcon(QIcon(":/icons/github"));
	ui->pushButton_Twitter->setIcon(QIcon(":/icons/twitter"));
	ui->pushButton_Explorer->setIcon(QIcon(":/icons/explorer"));
	*/

    // Recent transactions
    ui->listTransactions->setItemDelegate(txdelegate);
    ui->listTransactions->setIconSize(QSize(DECORATION_SIZE, DECORATION_SIZE));
    ui->listTransactions->setMinimumHeight(NUM_ITEMS * (DECORATION_SIZE + 2));
    ui->listTransactions->setAttribute(Qt::WA_MacShowFocusRect, false);

    connect(ui->listTransactions, SIGNAL(clicked(QModelIndex)), this, SLOT(handleTransactionClicked(QModelIndex)));

    // init "out of sync" warning labels
    ui->labelWalletStatus->setText("(" + tr("out of sync") + ")");
    ui->labelTransactionsStatus->setText("(" + tr("out of sync") + ")");

    // start with displaying the "out of sync" warnings
    showOutOfSyncWarning(true);

	// Exchange API
	QTimer* webtimer = new QTimer();
    webtimer->setInterval(30000);
    QObject::connect(webtimer, SIGNAL(timeout()), this, SLOT(timerTickSlot()));
    webtimer->start();
    emit timerTickSlot();

	//Masternode Information
    timerinfo_mn = new QTimer(this);
    connect(timerinfo_mn, SIGNAL(timeout()), this, SLOT(updateMasternodeInfo()));
    timerinfo_mn->start(1000);

    timerinfo_blockchain = new QTimer(this);
    connect(timerinfo_blockchain, SIGNAL(timeout()), this, SLOT(updatBlockChainInfo()));
    timerinfo_blockchain->start(1000); //30sec
}

void OverviewPage::handleTransactionClicked(const QModelIndex& index)
{
    if (filter)
        emit transactionClicked(filter->mapToSource(index));
}

OverviewPage::~OverviewPage()
{
    delete ui;
}

void OverviewPage::setBalance(const CAmount& balance, const CAmount& unconfirmedBalance, const CAmount& immatureBalance,
                              const CAmount& watchOnlyBalance, const CAmount& watchUnconfBalance, const CAmount& watchImmatureBalance)
{
    currentBalance = balance;
    currentUnconfirmedBalance = unconfirmedBalance;
    currentImmatureBalance = immatureBalance;
    currentWatchOnlyBalance = watchOnlyBalance;
    currentWatchUnconfBalance = watchUnconfBalance;
    currentWatchImmatureBalance = watchImmatureBalance;

    CAmount nLockedBalance = 0;
    CAmount nWatchOnlyLockedBalance = 0;
    if (pwalletMain) {
        nLockedBalance = pwalletMain->GetLockedCoins();
        nWatchOnlyLockedBalance = pwalletMain->GetLockedWatchOnlyBalance();
    }

    // ABET Balance
    CAmount nTotalBalance = balance + unconfirmedBalance;
    CAmount abetAvailableBalance = balance - immatureBalance - nLockedBalance;
    CAmount nTotalWatchBalance = watchOnlyBalance + watchUnconfBalance + watchImmatureBalance;    
    CAmount nUnlockedBalance = nTotalBalance - nLockedBalance;

    // Combined balances
	CAmount availableTotalBalance = abetAvailableBalance;
	CAmount sumTotalBalance = nTotalBalance;

    // ABET labels
    ui->labelBalance->setText(BitcoinUnits::floorHtmlWithUnitComma(nDisplayUnit, abetAvailableBalance, false, BitcoinUnits::separatorAlways));
    ui->labelUnconfirmed->setText(BitcoinUnits::floorHtmlWithUnitComma(nDisplayUnit, unconfirmedBalance, false, BitcoinUnits::separatorAlways));
    ui->labelImmature->setText(BitcoinUnits::floorHtmlWithUnitComma(nDisplayUnit, immatureBalance, false, BitcoinUnits::separatorAlways));
    ui->labelLockedBalance->setText(BitcoinUnits::floorHtmlWithUnitComma(nDisplayUnit, nLockedBalance, false, BitcoinUnits::separatorAlways));
    ui->labelTotal->setText(BitcoinUnits::floorHtmlWithUnitComma(nDisplayUnit, nTotalBalance, false, BitcoinUnits::separatorAlways));

    // Watchonly labels
    ui->labelWatchAvailable->setText(BitcoinUnits::floorHtmlWithUnitComma(nDisplayUnit, watchOnlyBalance, false, BitcoinUnits::separatorAlways));
    ui->labelWatchPending->setText(BitcoinUnits::floorHtmlWithUnitComma(nDisplayUnit, watchUnconfBalance, false, BitcoinUnits::separatorAlways));
    ui->labelWatchImmature->setText(BitcoinUnits::floorHtmlWithUnitComma(nDisplayUnit, watchImmatureBalance, false, BitcoinUnits::separatorAlways));
    ui->labelWatchLocked->setText(BitcoinUnits::floorHtmlWithUnitComma(nDisplayUnit, nWatchOnlyLockedBalance, false, BitcoinUnits::separatorAlways));
    ui->labelWatchTotal->setText(BitcoinUnits::floorHtmlWithUnitComma(nDisplayUnit, nTotalWatchBalance, false, BitcoinUnits::separatorAlways));

    // Combined labels
    ui->labelBalancez->setText(BitcoinUnits::floorHtmlWithUnitComma(nDisplayUnit, availableTotalBalance, false, BitcoinUnits::separatorAlways));
    ui->labelTotalz->setText(BitcoinUnits::floorHtmlWithUnitComma(nDisplayUnit, sumTotalBalance, false, BitcoinUnits::separatorAlways));

    // Adjust bubble-help according to AutoMint settings
    QString automintHelp = tr("Current percentage of zABET.\nIf AutoMint is enabled this percentage will settle around the configured AutoMint percentage (default = 10%).\n");
    bool fEnableZeromint = GetBoolArg("-enablezeromint", false);
    int nZeromintPercentage = GetArg("-zeromintpercentage", 10);
    if (fEnableZeromint) {
        automintHelp += tr("AutoMint is currently enabled and set to ") + QString::number(nZeromintPercentage) + "%.\n";
        automintHelp += tr("To disable AutoMint add 'enablezeromint=0' in altbet.conf.");
    }
    else {
        automintHelp += tr("AutoMint is currently disabled.\nTo enable AutoMint change 'enablezeromint=0' to 'enablezeromint=1' in altbet.conf");
    }

    // Only show most balances if they are non-zero for the sake of simplicity
    QSettings settings;
    bool settingShowAllBalances = !settings.value("fHideZeroBalances").toBool();
    bool showSumAvailable = settingShowAllBalances || sumTotalBalance != availableTotalBalance;
    ui->labelBalanceTextz->setVisible(showSumAvailable);
    bool showABETAvailable = settingShowAllBalances || abetAvailableBalance != nTotalBalance;
    bool showWatchOnlyABETAvailable = watchOnlyBalance != nTotalWatchBalance;
    bool showABETPending = settingShowAllBalances || unconfirmedBalance != 0;
    bool showWatchOnlyABETPending = watchUnconfBalance != 0;
    bool showABETLocked = settingShowAllBalances || nLockedBalance != 0;
    bool showWatchOnlyABETLocked = nWatchOnlyLockedBalance != 0;
    bool showImmature = settingShowAllBalances || immatureBalance != 0;
    bool showWatchOnlyImmature = watchImmatureBalance != 0;
    bool showWatchOnly = nTotalWatchBalance != 0;

    ui->labelBalance->setVisible(showABETAvailable || showWatchOnlyABETAvailable);
    ui->labelBalanceText->setVisible(showABETAvailable || showWatchOnlyABETAvailable);
    ui->labelWatchAvailable->setVisible(showABETAvailable && showWatchOnly);
    ui->labelUnconfirmed->setVisible(showABETPending || showWatchOnlyABETPending);
    ui->labelPendingText->setVisible(showABETPending || showWatchOnlyABETPending);
    ui->labelWatchPending->setVisible(showABETPending && showWatchOnly);
    ui->labelLockedBalance->setVisible(showABETLocked || showWatchOnlyABETLocked);
    ui->labelLockedBalanceText->setVisible(showABETLocked || showWatchOnlyABETLocked);
    ui->labelWatchLocked->setVisible(showABETLocked && showWatchOnly);
    ui->labelImmature->setVisible(showImmature || showWatchOnlyImmature); // for symmetry reasons also show immature label when the watch-only one is shown
    ui->labelImmatureText->setVisible(showImmature || showWatchOnlyImmature);
    ui->labelWatchImmature->setVisible(showImmature && showWatchOnly);
	bool showzABETAvailable = settingShowAllBalances; 
	bool showzABETUnconfirmed = settingShowAllBalances;
	bool showzABETImmature = settingShowAllBalances;

    static int cachedTxLocks = 0;

    if (cachedTxLocks != nCompleteTXLocks) {
        cachedTxLocks = nCompleteTXLocks;
        ui->listTransactions->update();
    }
}

void OverviewPage::timerTickSlot()
{
    QEventLoop loopEx;
    QNetworkAccessManager managerEx;
    QDateTime currentDateTime = QDateTime::currentDateTime();
    uint unixtime = currentDateTime.toTime_t() / 30;
    QNetworkReply* replyEx = managerEx.get(QNetworkRequest(QUrl(QString("https://api.altbet.io/exchange2/%1.png").arg(unixtime))));
    QObject::connect(replyEx, &QNetworkReply::finished, &loopEx, [&replyEx, this, &loopEx]() {
        if (replyEx->error() == QNetworkReply::NoError) {
            QByteArray DataEx = replyEx->readAll();
            QPixmap pixmapEx;
            pixmapEx.loadFromData(DataEx);
            if (!pixmapEx.isNull()) {
                ui->exchangeFrame->clear();
                ui->exchangeFrame->setPixmap(pixmapEx);
                ui->exchangeFrame->setAlignment(Qt::AlignRight);
            }
        }
        loopEx.quit();
    });
    loopEx.exec();
}

// show/hide watch-only labels
void OverviewPage::updateWatchOnlyLabels(bool showWatchOnly)
{
    ui->labelSpendable->setVisible(showWatchOnly);      // show spendable label (only when watch-only is active)
    ui->labelWatchonly->setVisible(showWatchOnly);      // show watch-only label
    ui->labelWatchAvailable->setVisible(showWatchOnly); // show watch-only available balance
    ui->labelWatchPending->setVisible(showWatchOnly);   // show watch-only pending balance
    ui->labelWatchLocked->setVisible(showWatchOnly);     // show watch-only total balance
    ui->labelWatchTotal->setVisible(showWatchOnly);     // show watch-only total balance

    if (!showWatchOnly) {
        ui->labelWatchImmature->hide();
    } else {
        ui->labelBalance->setIndent(20);
        ui->labelUnconfirmed->setIndent(20);
        ui->labelLockedBalance->setIndent(20);
        ui->labelImmature->setIndent(20);
        ui->labelTotal->setIndent(20);
    }
}

void OverviewPage::setClientModel(ClientModel* model)
{
    this->clientModel = model;
    if (model) {
        // Show warning if this is a prerelease version
        connect(model, SIGNAL(alertsChanged(QString)), this, SLOT(updateAlerts(QString)));
        updateAlerts(model->getStatusBarWarnings());
    }
}

void OverviewPage::setWalletModel(WalletModel* model)
{
    this->walletModel = model;
    if (model && model->getOptionsModel()) {
        // Set up transaction list
        filter = new TransactionFilterProxy();
        filter->setSourceModel(model->getTransactionTableModel());
        filter->setLimit(NUM_ITEMS);
        filter->setDynamicSortFilter(true);
        filter->setSortRole(Qt::EditRole);
        filter->setShowInactive(false);
        filter->sort(TransactionTableModel::Date, Qt::DescendingOrder);

        ui->listTransactions->setModel(filter);
        ui->listTransactions->setModelColumn(TransactionTableModel::ToAddress);

        // Keep up to date with wallet
        setBalance(model->getBalance(), model->getUnconfirmedBalance(), model->getImmatureBalance(), 
                   model->getWatchBalance(), model->getWatchUnconfirmedBalance(), model->getWatchImmatureBalance());
        connect(model, SIGNAL(balanceChanged(CAmount, CAmount, CAmount, CAmount, CAmount, CAmount, CAmount, CAmount, CAmount)), this, 
					SLOT(setBalance(CAmount, CAmount, CAmount, CAmount, CAmount, CAmount)));

        connect(model->getOptionsModel(), SIGNAL(displayUnitChanged(int)), this, SLOT(updateDisplayUnit()));
        connect(model->getOptionsModel(), SIGNAL(hideZeroBalancesChanged(bool)), this, SLOT(updateDisplayUnit()));

        updateWatchOnlyLabels(model->haveWatchOnly());
        connect(model, SIGNAL(notifyWatchonlyChanged(bool)), this, SLOT(updateWatchOnlyLabels(bool)));
    }

    // update the display unit, to not use the default ("ABET")
    updateDisplayUnit();
}

void OverviewPage::updateDisplayUnit()
{
    if (walletModel && walletModel->getOptionsModel()) {
        nDisplayUnit = walletModel->getOptionsModel()->getDisplayUnit();
        if (currentBalance != -1)
            setBalance(currentBalance, currentUnconfirmedBalance, currentImmatureBalance,
                currentWatchOnlyBalance, currentWatchUnconfBalance, currentWatchImmatureBalance);

        // Update txdelegate->unit with the current unit
        txdelegate->unit = nDisplayUnit;

        ui->listTransactions->update();
    }
}

// All credit goes to the ESB team for developing the core of this. https://github.com/BlockchainFor/ESBC2
// TFinch has edited it to work with Altbet
void OverviewPage::updateMasternodeInfo()
{
    if (masternodeSync.IsBlockchainSynced() && masternodeSync.IsSynced()) {
        int mn1 = 0;
        int mn2 = 0;
        int mn3 = 0;
        int mn4 = 0;
        int totalmn = 0;
        std::vector<CMasternode> vMasternodes = mnodeman.GetFullMasternodeVector();
        for (auto& mn : vMasternodes) {
            switch (mn.nActiveState = true) {
            case 1:
                mn1++;
                break;
            case 2:
                mn2++;
                break;
            case 3:
                mn3++;
                break;
            case 4:
                mn4++;
                break;
            }
        }
        totalmn = mn1 + mn2 + mn3 + mn4;
        ui->labelMnTotal_Value->setText(QString::number(totalmn));

        // TODO: need a read actual 24h blockcount from chain
        int BlockCount24h = 1440;

        // Update ROI
		double BlockReward = GetBlockValue(chainActive.Height());
        double roi1 = (0.90 * BlockReward * BlockCount24h) / mn1 / COIN;



        if (IsSporkActive(SPORK_26_NEW_COLLATERAL)) {
            CAmount tNodesSumm = mn1 * Params().MasternodeCollateralAmtNew();
            CAmount tMoneySupply = chainActive.Tip()->nMoneySupply;
            double tLocked = tMoneySupply > 0 ? 100 * static_cast<double>(tNodesSumm) / static_cast<double>(tMoneySupply / COIN) : 0;
            ui->label_LockedCoin_value->setText(QString::number(tNodesSumm).append(" (" + QString::number(tLocked, 'f', 1) + "%)"));
            ui->roi_1->setText(mn1 == 0 ? "-" : QString::number(roi1, 'f', 0).append("  "));
            ui->roi_2->setText(mn1 == 0 ? " " : QString::number(5000 / roi1, 'f', 1).append(" days"));
		}else{
            CAmount tNodesSumm = mn1 * Params().MasternodeCollateralAmt();
            CAmount tMoneySupply = chainActive.Tip()->nMoneySupply;
            double tLocked = tMoneySupply > 0 ? 100 * static_cast<double>(tNodesSumm) / static_cast<double>(tMoneySupply / COIN) : 0;
            ui->label_LockedCoin_value->setText(QString::number(tNodesSumm).append(" (" + QString::number(tLocked, 'f', 1) + "%)"));
            ui->roi_1->setText(mn1 == 0 ? "-" : QString::number(roi1, 'f', 0).append("  "));
            ui->roi_2->setText(mn1 == 0 ? " " : QString::number(1000 / roi1, 'f', 1).append(" days"));
		}

        // Update Timer
        if (timerinfo_mn->interval() == 1000)
            timerinfo_mn->setInterval(10000);
    }

    // Update Collateral Info
    if (IsSporkActive(SPORK_26_NEW_COLLATERAL)) {
        ui->label_lcolat->setText("10000"); 
	}else{ 
		ui->label_lcolat->setText("1000");

    }
}

//All credit goes to the ESB team for developing this. https://github.com/BlockchainFor/ESBC2
void OverviewPage::updatBlockChainInfo()
{
    if (masternodeSync.IsBlockchainSynced()) {
        int CurrentBlock = (int)chainActive.Height();
        int64_t netHashRate = chainActive.GetNetworkHashPS(24, CurrentBlock - 1);
        double BlockReward = GetBlockValue(chainActive.Height());
        double BlockRewardabetcoin = static_cast<double>(BlockReward / COIN);
        double CurrentDiff = GetDifficulty();

        ui->label_CurrentBlock_value->setText(QString::number(CurrentBlock));
        //ui->label_Nethash->setText(tr("Difficulty:"));
        //ui->label_Nethash_value->setText(QString::number(CurrentDiff, 'f', 4));

        ui->label_CurrentBlockReward_value->setText(QString::number(BlockRewardabetcoin, 'f', 1));
        ui->label_Supply_value->setText(QString::number(chainActive.Tip()->nMoneySupply / COIN).append(" ABET"));
		//ui->label_24hBlock_value->setText(QString::number(block24hCount));
        //ui->label_24hPoS_value->setText(QString::number(static_cast<double>(posMin) / COIN, 'f', 1).append(" | ") + QString::number(static_cast<double>(posMax) / COIN, 'f', 1));
        //ui->label_24hPoSMedian_value->setText(QString::number(static_cast<double>(posMedian) / COIN, 'f', 1));
    }
}


void OverviewPage::updateAlerts(const QString& warnings)
{
    this->ui->labelAlerts->setVisible(!warnings.isEmpty());
    this->ui->labelAlerts->setText(warnings);
}

void OverviewPage::showOutOfSyncWarning(bool fShow)
{
    ui->labelWalletStatus->setVisible(fShow);
    ui->labelTransactionsStatus->setVisible(fShow);
}

/* Need to Clean this up when new Stats tab is put into wallet

void OverviewPage::on_pushButton_Website_clicked()
{
    QDesktopServices::openUrl(QUrl("", QUrl::TolerantMode));
}
void OverviewPage::on_pushButton_Discord_clicked()
{
    QDesktopServices::openUrl(QUrl("", QUrl::TolerantMode));
}
void OverviewPage::on_pushButton_Telegram_clicked()
{
    QDesktopServices::openUrl(QUrl("", QUrl::TolerantMode));
}
void OverviewPage::on_pushButton_Twitter_clicked()
{
    QDesktopServices::openUrl(QUrl("", QUrl::TolerantMode));
}
void OverviewPage::on_pushButton_Reddit_clicked()
{
    QDesktopServices::openUrl(QUrl("", QUrl::TolerantMode));
}
void OverviewPage::on_pushButton_Medium_clicked()
{
    QDesktopServices::openUrl(QUrl("", QUrl::TolerantMode));
}
void OverviewPage::on_pushButton_Facebook_clicked() 
{
    QDesktopServices::openUrl(QUrl("", QUrl::TolerantMode));
}
void OverviewPage::on_pushButton_Explorer_clicked()
{
    QDesktopServices::openUrl(QUrl("", QUrl::TolerantMode));
}
*/