package ru.nstu.netifood;

import android.app.Activity;
import android.app.AlertDialog;
import android.content.ActivityNotFoundException;
import android.content.Intent;
import android.content.SharedPreferences;
import android.graphics.Bitmap;
import android.net.Uri;
import android.os.Bundle;
import android.text.InputType;
import android.text.TextUtils;
import android.view.Gravity;
import android.view.View;
import android.webkit.CookieManager;
import android.webkit.WebChromeClient;
import android.webkit.WebResourceError;
import android.webkit.WebResourceRequest;
import android.webkit.WebSettings;
import android.webkit.WebView;
import android.webkit.WebViewClient;
import android.widget.EditText;
import android.widget.FrameLayout;
import android.widget.ProgressBar;
import android.widget.Toast;

/**
 * Android-оболочка для NETI Food.
 * Открывает веб-интерфейс сервера app.py (FastAPI) внутри приложения.
 * Адрес сервера задаётся при первом запуске и меняется через кнопку «Назад»
 * на главном экране или со страницы ошибки подключения.
 */
public class MainActivity extends Activity {

    private static final String PREFS = "neti_food";
    private static final String KEY_URL = "server_url";
    private static final String DEFAULT_URL = "http://192.168.0.100:8000";

    private WebView webView;
    private ProgressBar progress;
    private String serverUrl;

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);

        FrameLayout root = new FrameLayout(this);
        webView = new WebView(this);
        root.addView(webView, new FrameLayout.LayoutParams(
                FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.MATCH_PARENT));

        progress = new ProgressBar(this, null, android.R.attr.progressBarStyleHorizontal);
        progress.setMax(100);
        progress.setIndeterminate(false);
        FrameLayout.LayoutParams lp = new FrameLayout.LayoutParams(
                FrameLayout.LayoutParams.MATCH_PARENT, dp(4), Gravity.TOP);
        root.addView(progress, lp);
        setContentView(root);

        setupWebView();

        serverUrl = getSharedPreferences(PREFS, MODE_PRIVATE).getString(KEY_URL, null);
        if (savedInstanceState != null && serverUrl != null) {
            webView.restoreState(savedInstanceState);
        } else if (serverUrl == null) {
            askServerUrl(true);
        } else {
            loadServer();
        }
    }

    private void setupWebView() {
        WebSettings s = webView.getSettings();
        s.setJavaScriptEnabled(true);
        s.setDomStorageEnabled(true);
        s.setDatabaseEnabled(true);
        s.setLoadWithOverviewMode(true);
        s.setUseWideViewPort(true);
        s.setMediaPlaybackRequiresUserGesture(false);
        s.setMixedContentMode(WebSettings.MIXED_CONTENT_ALWAYS_ALLOW);
        s.setCacheMode(WebSettings.LOAD_DEFAULT);

        CookieManager.getInstance().setAcceptCookie(true);
        CookieManager.getInstance().setAcceptThirdPartyCookies(webView, true);

        webView.setWebViewClient(new WebViewClient() {
            @Override
            public boolean shouldOverrideUrlLoading(WebView view, WebResourceRequest request) {
                return handleUrl(request.getUrl());
            }

            @Override
            public void onPageStarted(WebView view, String url, Bitmap favicon) {
                progress.setVisibility(View.VISIBLE);
            }

            @Override
            public void onPageFinished(WebView view, String url) {
                progress.setVisibility(View.GONE);
            }

            @Override
            public void onReceivedError(WebView view, WebResourceRequest request, WebResourceError error) {
                if (request.isForMainFrame()) {
                    showErrorPage(String.valueOf(error.getDescription()));
                }
            }
        });

        webView.setWebChromeClient(new WebChromeClient() {
            @Override
            public void onProgressChanged(WebView view, int newProgress) {
                progress.setProgress(newProgress);
            }
        });

        // Файлы (например, экспорт CSV) открываем в системном браузере.
        webView.setDownloadListener((url, userAgent, contentDisposition, mimeType, length) ->
                openExternal(Uri.parse(url)));
    }

    /** true — ссылку обработали сами, false — пусть WebView откроет её внутри приложения. */
    private boolean handleUrl(Uri uri) {
        String scheme = uri.getScheme() == null ? "" : uri.getScheme();
        if ("neti".equals(scheme)) {
            if ("settings".equals(uri.getHost())) {
                askServerUrl(false);
            } else {
                loadServer();
            }
            return true;
        }
        if (("http".equals(scheme) || "https".equals(scheme)) && serverUrl != null) {
            String serverHost = Uri.parse(serverUrl).getHost();
            if (serverHost != null && serverHost.equalsIgnoreCase(uri.getHost())) {
                return false;
            }
        }
        openExternal(uri);
        return true;
    }

    private void loadServer() {
        if (serverUrl == null) {
            askServerUrl(true);
            return;
        }
        webView.clearHistory();
        webView.loadUrl(serverUrl + "/");
    }

    private void askServerUrl(boolean firstRun) {
        EditText input = new EditText(this);
        input.setInputType(InputType.TYPE_CLASS_TEXT | InputType.TYPE_TEXT_VARIATION_URI);
        input.setSingleLine(true);
        input.setText(serverUrl != null ? serverUrl : DEFAULT_URL);
        input.setSelection(input.getText().length());

        FrameLayout box = new FrameLayout(this);
        box.setPadding(dp(20), dp(8), dp(20), 0);
        box.addView(input);

        AlertDialog.Builder b = new AlertDialog.Builder(this)
                .setTitle("Адрес сервера NETI Food")
                .setMessage("Компьютер с запущенным app.py и телефон должны быть в одной сети "
                        + "(или сервер должен быть доступен из интернета).")
                .setView(box)
                .setCancelable(!firstRun)
                .setPositiveButton("Подключиться", (d, w) -> {
                    String url = normalizeUrl(input.getText().toString());
                    if (url == null) {
                        Toast.makeText(this, "Введите адрес сервера", Toast.LENGTH_SHORT).show();
                        askServerUrl(firstRun);
                        return;
                    }
                    serverUrl = url;
                    getSharedPreferences(PREFS, MODE_PRIVATE).edit().putString(KEY_URL, url).apply();
                    loadServer();
                });
        if (!firstRun) {
            b.setNegativeButton("Отмена", null);
        }
        b.show();
    }

    private static String normalizeUrl(String raw) {
        String url = raw == null ? "" : raw.trim();
        if (TextUtils.isEmpty(url)) return null;
        if (!url.startsWith("http://") && !url.startsWith("https://")) {
            url = "http://" + url;
        }
        while (url.endsWith("/")) {
            url = url.substring(0, url.length() - 1);
        }
        return url;
    }

    private void showErrorPage(String reason) {
        String safeReason = TextUtils.htmlEncode(reason == null ? "" : reason);
        String safeUrl = TextUtils.htmlEncode(serverUrl == null ? "" : serverUrl);
        String html = "<!doctype html><html lang='ru'><head><meta charset='utf-8'>"
                + "<meta name='viewport' content='width=device-width,initial-scale=1'>"
                + "<style>"
                + "body{margin:0;font-family:sans-serif;background:#f8fafc;color:#0f172a;"
                + "display:flex;min-height:100vh;align-items:center;justify-content:center}"
                + ".c{max-width:420px;padding:28px;text-align:center}"
                + "h1{font-size:22px;margin:0 0 10px}p{color:#475569;line-height:1.5}"
                + "code{background:#e2e8f0;padding:2px 6px;border-radius:6px;word-break:break-all}"
                + "a{display:block;margin:12px 0;padding:14px;border-radius:14px;text-decoration:none;font-weight:600}"
                + ".p{background:#be123c;color:#fff}.s{background:#fff;color:#be123c;border:2px solid #be123c}"
                + "</style></head><body><div class='c'>"
                + "<div style='font-size:48px'>🍽️</div>"
                + "<h1>Нет связи с сервером</h1>"
                + "<p>Не удалось открыть <code>" + safeUrl + "</code></p>"
                + "<p style='font-size:13px'>" + safeReason + "</p>"
                + "<p style='font-size:13px'>Проверьте, что app.py запущен и телефон в той же сети Wi-Fi.</p>"
                + "<a class='p' href='neti://retry'>Повторить</a>"
                + "<a class='s' href='neti://settings'>Изменить адрес сервера</a>"
                + "</div></body></html>";
        webView.loadDataWithBaseURL(null, html, "text/html", "UTF-8", null);
    }

    private void openExternal(Uri uri) {
        try {
            startActivity(new Intent(Intent.ACTION_VIEW, uri));
        } catch (ActivityNotFoundException e) {
            Toast.makeText(this, "Нет приложения, чтобы открыть ссылку", Toast.LENGTH_SHORT).show();
        }
    }

    @Override
    public void onBackPressed() {
        if (webView.canGoBack()) {
            webView.goBack();
            return;
        }
        new AlertDialog.Builder(this)
                .setTitle("NETI Food")
                .setItems(new String[]{"Выйти", "Изменить адрес сервера", "Обновить страницу"}, (d, which) -> {
                    if (which == 0) finish();
                    else if (which == 1) askServerUrl(false);
                    else loadServer();
                })
                .show();
    }

    @Override
    protected void onSaveInstanceState(Bundle outState) {
        super.onSaveInstanceState(outState);
        webView.saveState(outState);
    }

    @Override
    protected void onPause() {
        super.onPause();
        webView.onPause();
        CookieManager.getInstance().flush();
    }

    @Override
    protected void onResume() {
        super.onResume();
        webView.onResume();
    }

    @Override
    protected void onDestroy() {
        webView.destroy();
        super.onDestroy();
    }

    private int dp(int value) {
        return Math.round(value * getResources().getDisplayMetrics().density);
    }
}
