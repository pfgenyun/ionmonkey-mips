/* Any copyright is dedicated to the Public Domain.
   http://creativecommons.org/publicdomain/zero/1.0/ */

// Tests that the developer toolbar works properly

const TEST_URI = "data:text/html;charset=utf-8,<p>Tooltip Tests</p>";

function test() {
  addTab(TEST_URI, function(browser, tab) {
    info("Starting browser_toolbar_tooltip.js");
    openTest();
  });
}

function openTest() {
  ok(!DeveloperToolbar.visible, "DeveloperToolbar is not visible in runTest");

  oneTimeObserve(DeveloperToolbar.NOTIFICATIONS.SHOW, catchFail(runTest));
  document.getElementById("Tools:DevToolbar").doCommand();
}

function runTest() {
  let tooltipPanel = DeveloperToolbar.tooltipPanel;

  DeveloperToolbar.display.focusManager.helpRequest();
  DeveloperToolbar.display.inputter.setInput('help help');

  DeveloperToolbar.display.inputter.setCursor({ start: 'help help'.length });
  is(tooltipPanel._dimensions.start, 'help '.length,
          'search param start, when cursor at end');
  ok(getLeftMargin() > 30, 'tooltip offset, when cursor at end')

  DeveloperToolbar.display.inputter.setCursor({ start: 'help'.length });
  is(tooltipPanel._dimensions.start, 0,
          'search param start, when cursor at end of command');
  ok(getLeftMargin() > 9, 'tooltip offset, when cursor at end of command')

  DeveloperToolbar.display.inputter.setCursor({ start: 'help help'.length - 1 });
  is(tooltipPanel._dimensions.start, 'help '.length,
          'search param start, when cursor at penultimate position');
  ok(getLeftMargin() > 30, 'tooltip offset, when cursor at penultimate position')

  DeveloperToolbar.display.inputter.setCursor({ start: 0 });
  is(tooltipPanel._dimensions.start, 0,
          'search param start, when cursor at start');
  ok(getLeftMargin() > 9, 'tooltip offset, when cursor at start')

  finish();
}

function getLeftMargin() {
  let style = DeveloperToolbar.tooltipPanel._panel.style.marginLeft;
  return parseInt(style.slice(0, -2), 10);
}
